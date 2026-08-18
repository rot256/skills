#!/usr/bin/env sage
"""Exact XOR-AND graph synthesis under an AND-count objective.

An XAG gate multiplies two arbitrary affine forms over the primary inputs and
earlier gate outputs.  Thus each gate is one nonlinear operation, while XOR
and NOT remain free in the default objective.  Optional XOR optimization is a
lexicographic second phase after the AND count has been fixed.

Truth-table index ``i`` uses the little-endian assignment
``x[j] = (i >> j) & 1``, matching Sage's truth-table storage convention.

Run without arguments for deterministic self-tests.  Use ``--help`` for the
small-instance command-line interface, or ``load`` this file and call
``synthesize`` / ``search_minimum``.
"""

import argparse
import json
import os
import sys

import pycosat
from sage.all import BooleanPolynomialRing
from sage.crypto.boolean_function import BooleanFunction
from sage.sat.converters.polybori import CNFEncoder

_cwd_scripts = os.path.join(os.getcwd(), "scripts")
if os.path.isdir(_cwd_scripts) and _cwd_scripts not in sys.path:
    sys.path.insert(0, _cwd_scripts)
try:
    from xag import affine, dumps_xag, make_xag, truth_tables, xag_metrics
except ImportError:  # ``load('scripts/exact_xag.sage')`` from the repository root
    from scripts.xag import affine, dumps_xag, make_xag, truth_tables, xag_metrics


class _ClauseCollector:
    """The small Sage SAT-solver interface CNFEncoder needs."""

    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def var(self, decision=None):
        self.nvars += 1
        return self.nvars

    def add_clause(self, literals):
        self.clauses.append([int(literal) for literal in literals])


def _table(value, num_inputs, what="truth table"):
    size = 1 << num_inputs
    if isinstance(value, BooleanFunction):
        bits = [int(x) for x in value.truth_table()]
    elif hasattr(value, "truth_table"):
        bits = [int(x) for x in value.truth_table()]
    else:
        bits = [int(x) for x in value]
    if len(bits) != size:
        raise ValueError("%s must have %d entries, got %d" % (what, size, len(bits)))
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("%s entries must be bits" % what)
    return bits


def _problem(num_inputs, outputs, care_masks=None):
    n = int(num_inputs)
    if n < 0:
        raise ValueError("num_inputs must be non-negative")
    tables = [_table(output, n) for output in outputs]
    if not tables:
        raise ValueError("at least one output is required")
    if care_masks is None:
        masks = [[1] * (1 << n) for _ in tables]
    else:
        if len(care_masks) != len(tables):
            raise ValueError("provide one care mask per output")
        masks = [_table(mask, n, "care mask") for mask in care_masks]
    return n, tables, masks


def _selector_names(n, num_outputs, and_count):
    names = []
    forms = []
    for gate in range(and_count):
        for side in ("l", "r"):
            form = ["s_g%d_%s_%d" % (gate, side, term) for term in range(n + gate + 1)]
            names.extend(form)
            forms.append(form)
    for output in range(num_outputs):
        form = ["s_o%d_%d" % (output, term) for term in range(n + and_count + 1)]
        names.extend(form)
        forms.append(form)
    return names, forms


def _encode(n, tables, masks, and_count, sample_points):
    selector_names, objective_forms = _selector_names(n, len(tables), and_count)
    value_names = [
        "v_g%d_p%d" % (gate, point)
        for point in sample_points for gate in range(and_count)
    ]
    names = selector_names + value_names
    # BooleanPolynomialRing accepts zero variables poorly; every useful problem
    # has at least one output-selector variable, even at n=k=0.
    ring = BooleanPolynomialRing(len(names), names=names)
    variables = dict(zip(names, ring.gens()))
    equations = []

    for point in sample_points:
        inputs = [(point >> i) & 1 for i in range(n)]
        gate_values = []
        for gate in range(and_count):
            left = variables["s_g%d_l_0" % gate]
            right = variables["s_g%d_r_0" % gate]
            for i, bit in enumerate(inputs):
                if bit:
                    left += variables["s_g%d_l_%d" % (gate, i + 1)]
                    right += variables["s_g%d_r_%d" % (gate, i + 1)]
            for earlier, value in enumerate(gate_values):
                left += variables["s_g%d_l_%d" % (gate, n + earlier + 1)] * value
                right += variables["s_g%d_r_%d" % (gate, n + earlier + 1)] * value
            gate_value = variables["v_g%d_p%d" % (gate, point)]
            equations.append(gate_value + left * right)
            gate_values.append(gate_value)

        for output, (table, mask) in enumerate(zip(tables, masks)):
            if not mask[point]:
                continue
            value = variables["s_o%d_0" % output] + table[point]
            for i, bit in enumerate(inputs):
                if bit:
                    value += variables["s_o%d_%d" % (output, i + 1)]
            for gate, gate_value in enumerate(gate_values):
                value += variables["s_o%d_%d" % (output, n + gate + 1)] * gate_value
            equations.append(value)

    collector = _ClauseCollector()
    encoder = CNFEncoder(
        collector, ring, max_vars_sparse=6, use_xor_clauses=False,
        random_seed=int(16)
    )
    encoder(equations)
    # CNFEncoder allocates the ring generators first and in generator order.
    selector_vars = {name: variables[name].lm().index() + 1 for name in selector_names}
    objective_vars = [[selector_vars[name] for name in form] for form in objective_forms]
    return collector.clauses, collector.nvars, selector_vars, objective_vars


def _new_var(state):
    state[0] += 1
    return state[0]


def _equiv_or(clauses, z, a, b):
    clauses.extend(([-a, z], [-b, z], [a, b, -z]))


def _equiv_and(clauses, z, a, b):
    clauses.extend(([-a, -b, z], [a, -z], [b, -z]))


def _equiv_or_and(clauses, z, a, b, x):
    """Encode z <-> a OR (b AND x)."""
    clauses.extend(([-a, z], [-b, -x, z], [-z, a, b], [-z, a, x]))


def _thresholds(bits, clauses, state, limit=None):
    """Return literals for weight(bits)>=1, >=2, ... (up to ``limit``)."""
    if not bits:
        return []
    previous = [bits[0]]
    for i, bit in enumerate(bits[1:], start=2):
        width = i if limit is None else min(i, limit)
        current = []
        z = _new_var(state)
        _equiv_or(clauses, z, previous[0], bit)
        current.append(z)
        for threshold in range(2, width + 1):
            z = _new_var(state)
            if threshold == i:
                _equiv_and(clauses, z, previous[threshold - 2], bit)
            else:
                _equiv_or_and(
                    clauses, z, previous[threshold - 1],
                    previous[threshold - 2], bit,
                )
            current.append(z)
        previous = current
    return previous


def _add_xor_bound(base_clauses, num_vars, objective_forms, bound):
    """Bound sum(max(0, affine-form weight - 1)) by ``bound``."""
    clauses = [list(clause) for clause in base_clauses]
    state = [num_vars]
    cost_literals = []
    for form in objective_forms:
        cost_literals.extend(_thresholds(form, clauses, state)[1:])
    if bound < 0:
        clauses.append([])
    elif bound < len(cost_literals):
        total = _thresholds(cost_literals, clauses, state, limit=bound + 1)
        clauses.append([-total[bound]])  # forbid total >= bound+1
    return clauses, state[0]


def _solve(clauses):
    # Sage preparses integer literals into ``Integer`` objects; pycosat's C API
    # intentionally accepts only native Python ints.
    model = pycosat.solve([[int(literal) for literal in clause] for clause in clauses])
    if model == "UNSAT":
        return None
    if model == "UNKNOWN":
        raise RuntimeError("SAT solver returned UNKNOWN")
    return {literal for literal in model if literal > 0}


def _decode(n, num_outputs, and_count, selector_vars, model, metadata=None):
    def selected(name):
        return selector_vars[name] in model

    gates = []
    for gate in range(and_count):
        sides = {}
        for side_name, short in (("left", "l"), ("right", "r")):
            constant = selected("s_g%d_%s_0" % (gate, short))
            terms = [
                signal for signal in range(n + gate)
                if selected("s_g%d_%s_%d" % (gate, short, signal + 1))
            ]
            sides[side_name] = affine(constant, terms)
        gates.append(sides)
    outputs = []
    for output in range(num_outputs):
        constant = selected("s_o%d_0" % output)
        terms = [
            signal for signal in range(n + and_count)
            if selected("s_o%d_%d" % (output, signal + 1))
        ]
        outputs.append(affine(constant, terms))
    return make_xag(n, gates, outputs, metadata=metadata)


def _counterexample(xag, tables, masks):
    actual = truth_tables(xag)
    for point in range(1 << xag["num_inputs"]):
        for output, (got, want, mask) in enumerate(zip(actual, tables, masks)):
            if mask[point] and got[point] != want[point]:
                return point, output
    return None


def _fixed_count(n, tables, masks, and_count, mode, optimize_xor, verbose=False):
    active = [
        point for point in range(1 << n)
        if any(mask[point] for mask in masks)
    ]
    if mode not in ("full", "cegar"):
        raise ValueError("mode must be 'full' or 'cegar'")
    if mode == "cegar" and optimize_xor:
        raise ValueError("XOR tie-breaking requires mode='full'")
    sample = list(active if mode == "full" else active[:1])

    while True:
        clauses, num_vars, selector_vars, objective_forms = _encode(
            n, tables, masks, and_count, sample
        )
        model = _solve(clauses)
        if model is None:
            return None
        candidate = _decode(n, len(tables), and_count, selector_vars, model)
        failure = _counterexample(candidate, tables, masks)
        if failure is not None:
            if mode == "full":
                raise AssertionError("decoded SAT model failed exhaustive verification")
            point, output = failure
            if point in sample:
                raise AssertionError("CEGAR model violates an encoded sample")
            sample.append(point)
            sample.sort()
            if verbose:
                print("CEGAR: added point %d (output %d)" % (point, output), file=sys.stderr)
            continue

        if optimize_xor:
            best = candidate
            best_cost = xag_metrics(best)["xor_count"]
            low, high = 0, best_cost - 1
            while low <= high:
                bound = (low + high) // 2
                bounded, _ = _add_xor_bound(clauses, num_vars, objective_forms, bound)
                bounded_model = _solve(bounded)
                if bounded_model is None:
                    low = bound + 1
                else:
                    trial = _decode(n, len(tables), and_count, selector_vars, bounded_model)
                    if _counterexample(trial, tables, masks) is not None:
                        raise AssertionError("XOR-optimized model failed exhaustive verification")
                    best = trial
                    best_cost = xag_metrics(best)["xor_count"]
                    high = min(bound, best_cost) - 1
            candidate = best

        candidate["metadata"] = {
            "synthesis": {
                "mode": mode,
                "and_count_fixed": and_count,
                "xor_tiebreak": bool(optimize_xor),
                "verified_exhaustively": True,
            }
        }
        return make_xag(
            candidate["num_inputs"], candidate["gates"], candidate["outputs"],
            metadata=candidate["metadata"],
        )


def synthesize(num_inputs, outputs, care_masks=None, and_count=None,
               max_ands=None, mode="full", optimize_xor=False, verbose=False):
    """Synthesize an XAG, optionally proving the minimum AND count.

    If ``and_count`` is supplied, search exactly that many gates.  Otherwise
    budgets from zero through ``max_ands`` are proved UNSAT or solved in order.
    ``max_ands`` defaults to ``num_inputs`` as a small-instance safety bound.
    A ``None`` result proves no graph exists in the requested budget range.
    """
    n, tables, masks = _problem(num_inputs, outputs, care_masks)
    if and_count is not None:
        k = int(and_count)
        if k < 0:
            raise ValueError("and_count must be non-negative")
        return _fixed_count(n, tables, masks, k, mode, optimize_xor, verbose)
    return search_minimum(
        n, tables, masks, max_ands=max_ands, mode=mode,
        optimize_xor=optimize_xor, verbose=verbose,
    )


def search_minimum(num_inputs, outputs, care_masks=None, max_ands=None,
                   mode="full", optimize_xor=False, verbose=False):
    """Prove lower budgets UNSAT and return a minimum-AND XAG, or ``None``."""
    n, tables, masks = _problem(num_inputs, outputs, care_masks)
    limit = n if max_ands is None else int(max_ands)
    if limit < 0:
        raise ValueError("max_ands must be non-negative")
    for and_count in range(limit + 1):
        if verbose:
            print("trying AND count %d" % and_count, file=sys.stderr)
        xag = _fixed_count(
            n, tables, masks, and_count, mode, optimize_xor, verbose
        )
        if xag is not None:
            metadata = dict(xag.get("metadata", {}))
            metadata["synthesis"] = dict(metadata.get("synthesis", {}))
            metadata["synthesis"].update({
                "minimum_and_count_proved": True,
                "lower_budgets_unsat": list(range(and_count)),
            })
            return make_xag(n, xag["gates"], xag["outputs"], metadata=metadata)
    return None


def _parse_bits(text, size, what):
    raw = text.strip().replace("_", "").replace(",", "")
    if raw.startswith("0x"):
        value = int(raw, 16)
        if value >= (1 << size):
            raise ValueError("%s does not fit %d truth-table bits" % (what, size))
        return [(value >> i) & 1 for i in range(size)]
    if len(raw) != size or any(bit not in "01" for bit in raw):
        raise ValueError("%s must be %d binary digits" % (what, size))
    return [int(bit) for bit in raw]


def _self_test():
    xor2 = [0, 1, 1, 0]
    and2 = [0, 0, 0, 1]
    majority = [0, 0, 0, 1, 0, 1, 1, 1]

    zero = search_minimum(2, [xor2], max_ands=0)
    assert zero is not None and zero["metrics"]["and_count"] == 0
    assert truth_tables(zero) == [xor2]

    assert synthesize(2, [and2], and_count=0) is None
    one = search_minimum(2, [and2], max_ands=1)
    assert one is not None and one["metrics"]["and_count"] == 1
    assert truth_tables(one) == [and2]

    maj = search_minimum(3, [majority], max_ands=1)
    assert maj is not None and maj["metrics"]["and_count"] == 1

    shared_outputs = [and2, [0, 1, 0, 0]]  # x0*x1 and x0 XOR x0*x1
    shared = search_minimum(2, shared_outputs, max_ands=1)
    assert shared is not None and truth_tables(shared) == shared_outputs

    care = [1, 1, 1, 0]
    dont_care = search_minimum(2, [and2], [care], max_ands=0)
    assert dont_care is not None and dont_care["metrics"]["and_count"] == 0

    full = search_minimum(2, [and2], max_ands=1, mode="full")
    cegar = search_minimum(2, [and2], max_ands=1, mode="cegar")
    assert full["metrics"]["and_count"] == cegar["metrics"]["and_count"] == 1
    assert truth_tables(full) == truth_tables(cegar) == [and2]

    lex = search_minimum(3, [majority], max_ands=1, optimize_xor=True)
    assert lex is not None and lex["metrics"]["and_count"] == 1
    assert truth_tables(lex) == [majority]
    try:
        search_minimum(2, [and2], max_ands=1, mode="cegar", optimize_xor=True)
        raise AssertionError("CEGAR/XOR combination should be rejected")
    except ValueError as error:
        assert "requires mode='full'" in str(error)

    and3 = [0] * 7 + [1]
    assert synthesize(3, [and3], and_count=1) is None
    and3_xag = synthesize(3, [and3], and_count=2)
    assert and3_xag is not None and truth_tables(and3_xag) == [and3]

    quadratic = [
        (((point >> 0) & 1) * ((point >> 1) & 1) +
         ((point >> 2) & 1) * ((point >> 3) & 1)) % 2
        for point in range(16)
    ]
    assert synthesize(4, [quadratic], and_count=1) is None
    quadratic_xag = synthesize(4, [quadratic], and_count=2)
    assert quadratic_xag is not None and truth_tables(quadratic_xag) == [quadratic]
    print("exact_xag.sage: PASS")


def _main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--num-inputs", type=int)
    parser.add_argument(
        "--output", action="append",
        help="truth bits in table-index order, or a little-endian 0x integer; repeatable",
    )
    parser.add_argument(
        "--care", action="append",
        help="care-mask bits for the corresponding output; repeatable",
    )
    parser.add_argument("--and-count", type=int, help="search exactly this AND count")
    parser.add_argument("--max-ands", type=int, help="maximum budget for minimum search")
    parser.add_argument("--mode", choices=("full", "cegar"), default="full")
    parser.add_argument(
        "--optimize-xor", action="store_true",
        help="lexicographically minimize informational XOR count after fixing AND count",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--json", dest="json_path", help="also write the XAG JSON to this path")
    args = parser.parse_args(argv)
    if args.num_inputs is None and not args.output:
        _self_test()
        return 0
    if args.num_inputs is None or not args.output:
        parser.error("--num-inputs and at least one --output are required")
    size = 1 << args.num_inputs
    try:
        outputs = [_parse_bits(raw, size, "output") for raw in args.output]
        cares = None if args.care is None else [
            _parse_bits(raw, size, "care mask") for raw in args.care
        ]
        xag = synthesize(
            args.num_inputs, outputs, cares, and_count=args.and_count,
            max_ands=args.max_ands, mode=args.mode,
            optimize_xor=args.optimize_xor, verbose=args.verbose,
        )
    except ValueError as error:
        parser.error(str(error))
    if xag is None:
        print("UNSAT within requested AND budget", file=sys.stderr)
        return 1
    rendered = dumps_xag(xag)
    print(rendered)
    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    return 0


if os.path.basename(sys.argv[0]).startswith("exact_xag.sage"):
    _status = int(_main(sys.argv[1:]))
    if _status:
        raise SystemExit(_status)
