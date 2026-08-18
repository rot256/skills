#!/usr/bin/env sage
"""Exploit autosymmetry and D-reducibility of one Boolean truth table.

The tool uses the full translation-invariance subspace, not a sampled
symmetry, and the unique minimal affine hull of every nonempty on-set.
Truth-table index ``i`` uses ``x[j] = (i >> j) & 1``.

Run without arguments for deterministic self-tests.  Use ``--help`` for the
small single-output command-line interface.
"""

import argparse
import json
import operator
import os
import sys

from sage.repl.load import load as sage_load

_cwd_scripts = os.path.join(os.getcwd(), "scripts")
if os.path.isdir(_cwd_scripts) and _cwd_scripts not in sys.path:
    sys.path.insert(0, _cwd_scripts)
try:
    from xag import affine, make_xag, truth_tables
except ImportError:
    from scripts.xag import affine, make_xag, truth_tables


REPORT_FORMAT = "regular-xag-reduction"
REPORT_VERSION = 1
MAX_DEFAULT_INPUTS = 12
MAX_EXACT_LOCAL_INPUTS = 6


def _bits(value, width):
    return [int((int(value) >> i) & 1) for i in range(width)]


def _eval_form(form, point):
    value = int(form["constant"])
    for term in form["terms"]:
        value = operator.xor(value, (point >> term) & 1)
    return value


def _xor_forms(forms):
    constant = 0
    terms = set()
    for form in forms:
        constant = operator.xor(constant, int(form["constant"]))
        for term in form["terms"]:
            if term in terms:
                terms.remove(term)
            else:
                terms.add(term)
    return affine(constant, sorted(terms))


def _rref_basis(vectors, num_inputs):
    """Return a deterministic RREF row basis and its pivot columns."""
    rows = sorted(set(int(value) for value in vectors if int(value)))
    rank = 0
    pivots = []
    for column in range(num_inputs):
        pivot = next(
            (index for index in range(rank, len(rows))
             if rows[index] & (1 << column)),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for index in range(len(rows)):
            if index != rank and rows[index] & (1 << column):
                rows[index] = operator.xor(rows[index], rows[rank])
        pivots.append(column)
        rank += 1
    return rows[:rank], pivots


def _annihilator_basis(rref_rows, pivots, num_inputs):
    """Return a basis of linear forms whose common kernel is row span."""
    free = [column for column in range(num_inputs) if column not in pivots]
    forms = []
    for column in free:
        row = 1 << column
        for basis_index, pivot in enumerate(pivots):
            if rref_rows[basis_index] & (1 << column):
                row |= 1 << pivot
        forms.append(row)
    return forms


def _table_string(table):
    return "".join(str(int(bit)) for bit in table)


def _subspace_json(vectors, basis, num_inputs):
    return {
        "dimension": len(basis),
        "basis": [_bits(value, num_inputs) for value in basis],
        "vectors": [_bits(value, num_inputs) for value in vectors],
        "coordinate_order": "entries are [x0, x1, ...]",
    }


def autosymmetry_reduce(table, num_inputs):
    """Quotient by all translations ``a`` satisfying f(x)=f(x+a)."""
    size = 1 << num_inputs
    translations = [
        delta for delta in range(size)
        if all(
            table[point] == table[operator.xor(point, delta)]
            for point in range(size)
        )
    ]
    basis, pivots = _rref_basis(translations, num_inputs)
    quotient_rows = _annihilator_basis(basis, pivots, num_inputs)
    forms = [affine(0, [i for i in range(num_inputs) if row & (1 << i)])
             for row in quotient_rows]
    quotient = [None] * (1 << len(forms))
    for point in range(size):
        index = sum(_eval_form(form, point) << i for i, form in enumerate(forms))
        if quotient[index] is None:
            quotient[index] = int(table[point])
        elif quotient[index] != int(table[point]):
            raise AssertionError("translation quotient is not well-defined")
    if any(bit is None for bit in quotient):
        raise AssertionError("translation quotient map is not surjective")
    verified = all(
        table[point] == quotient[
            sum(_eval_form(form, point) << i for i, form in enumerate(forms))
        ]
        for point in range(size)
    )
    if not verified:
        raise AssertionError("autosymmetry lifting failed exhaustive verification")
    return {
        "translation_invariance_subspace": _subspace_json(
            translations, basis, num_inputs
        ),
        "quotient_num_inputs": len(forms),
        "reduction_forms": forms,
        "quotient_truth_table": _table_string(quotient),
        "identity": "f(x) = quotient(reduction_forms(x))",
        "verified_exhaustively": True,
        "_quotient_table": quotient,
    }


def _affine_hull(table, num_inputs):
    on_set = [point for point, bit in enumerate(table) if bit]
    if not on_set:
        return None
    anchor = on_set[0]
    basis, pivots = _rref_basis(
        [operator.xor(point, anchor) for point in on_set], num_inputs
    )
    free = [column for column in range(num_inputs) if column not in pivots]

    projection_forms = [
        affine((anchor >> pivot) & 1, [pivot]) for pivot in pivots
    ]
    membership_factors = []
    for column in free:
        constant = operator.xor(1, (anchor >> column) & 1)
        terms = [column]
        for basis_index, pivot in enumerate(pivots):
            if basis[basis_index] & (1 << column):
                terms.append(pivot)
                constant = operator.xor(
                    constant, (anchor >> pivot) & 1
                )
        membership_factors.append(affine(constant, terms))

    projection = []
    for coordinate in range(1 << len(basis)):
        point = anchor
        for i, row in enumerate(basis):
            if coordinate & (1 << i):
                point = operator.xor(point, row)
        projection.append(int(table[point]))

    def project(point):
        return sum(
            _eval_form(form, point) << i
            for i, form in enumerate(projection_forms)
        )

    def characteristic(point):
        return int(all(_eval_form(form, point) for form in membership_factors))

    verified = all(
        table[point] == characteristic(point) * projection[project(point)]
        for point in range(1 << num_inputs)
    )
    if not verified:
        raise AssertionError("D-reduction failed exhaustive verification")

    return {
        "anchor": _bits(anchor, num_inputs),
        "direction_basis": [_bits(row, num_inputs) for row in basis],
        "dimension": len(basis),
        "codimension": len(free),
        "canonical_input_indices": pivots,
        "noncanonical_input_indices": free,
        "membership_factors": membership_factors,
        "membership_factor_semantics": "each factor is 1 on A; chi_A is their AND",
        "membership_and_count_exact": max(len(free) - 1, 0),
        "projection": {
            "num_inputs": len(basis),
            "input_affine_forms": projection_forms,
            "truth_table": _table_string(projection),
        },
        "projection_coordinate_lift": "x = anchor + sum_i y[i] * direction_basis[i] over GF(2)",
        "identity": "f(x) = chi_A(x) * f_A(projection(x))",
        "verified_exhaustively": True,
        "_basis_masks": basis,
        "_projection_table": projection,
    }


def d_reduce(table, num_inputs):
    hull = _affine_hull(table, num_inputs)
    if hull is None:
        return {
            "status": "constant-zero",
            "is_d_reducible": bool(num_inputs > 0),
            "associated_affine_hull_exists": False,
            "affine_hull": None,
            "note": "The empty on-set has no unique nonempty minimal affine hull; use the zero XAG.",
            "zero_xag_and_count": 0,
            "verified_exhaustively": True,
        }
    projection_autosymmetry = autosymmetry_reduce(
        hull["_projection_table"], hull["dimension"]
    )
    public_hull = {key: value for key, value in hull.items()
                   if not key.startswith("_")}
    public_autosymmetry = {
        key: value for key, value in projection_autosymmetry.items()
        if not key.startswith("_")
    }
    return {
        "status": "nonempty-on-set",
        "is_d_reducible": hull["dimension"] < num_inputs,
        "affine_hull": public_hull,
        "projection_autosymmetry": public_autosymmetry,
        "verified_exhaustively": True,
        "_hull": hull,
        "_projection_autosymmetry": projection_autosymmetry,
    }


def _load_exact_search():
    candidates = [
        os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "exact_xag.sage"
        ),
        os.path.join(os.getcwd(), "scripts", "exact_xag.sage"),
    ]
    path = next((candidate for candidate in candidates
                 if os.path.exists(candidate)), None)
    if path is None:
        raise RuntimeError("exact_xag.sage is required for --exact-local")
    namespace = dict(globals())
    namespace["__name__"] = "regular_reduce_exact_library"
    sage_load(path, namespace, attach=False)
    if "search_minimum" not in namespace:
        raise RuntimeError("exact_xag.sage does not export search_minimum")
    return namespace["search_minimum"]


def _compose_forms(outer_forms, inner_forms):
    """Substitute ``inner_forms`` for the inputs of each outer form."""
    result = []
    for form in outer_forms:
        pieces = [affine(form["constant"], [])]
        pieces.extend(inner_forms[term] for term in form["terms"])
        result.append(_xor_forms(pieces))
    return result


def _embed_local_xag(local_xag, original_num_inputs, input_forms,
                     membership_factors, expected_table):
    """Lift a local exact XAG and compose it with affine-space membership."""
    local_n = local_xag["num_inputs"]
    if len(input_forms) != local_n or len(local_xag["outputs"]) != 1:
        raise ValueError("local XAG/input-form arity mismatch")
    gates = []
    local_gate_forms = []

    def substitute(form):
        pieces = [affine(form["constant"], [])]
        for signal in form["terms"]:
            if signal < local_n:
                pieces.append(input_forms[signal])
            else:
                pieces.append(local_gate_forms[signal - local_n])
        return _xor_forms(pieces)

    for gate in local_xag["gates"]:
        gates.append({"left": substitute(gate["left"]),
                      "right": substitute(gate["right"])})
        local_gate_forms.append(
            affine(0, [original_num_inputs + len(gates) - 1])
        )
    local_output = substitute(local_xag["outputs"][0])

    if not membership_factors:
        output = local_output
    else:
        characteristic = membership_factors[0]
        for factor in membership_factors[1:]:
            gates.append({"left": characteristic, "right": factor})
            characteristic = affine(0, [original_num_inputs + len(gates) - 1])
        local_table = truth_tables(local_xag)[0]
        if all(bit == 0 for bit in local_table):
            output = affine(0, [])
        elif all(bit == 1 for bit in local_table):
            output = characteristic
        else:
            gates.append({"left": characteristic, "right": local_output})
            output = affine(0, [original_num_inputs + len(gates) - 1])

    full = make_xag(
        original_num_inputs,
        gates,
        [output],
        metadata={
            "generator": "regular_reduce.sage",
            "construction": "D-reduction followed by projection autosymmetry",
            "optimality": "constructive upper bound; global optimality is not claimed",
            "verified_exhaustively": True,
        },
    )
    if truth_tables(full) != [list(expected_table)]:
        raise AssertionError("lifted full XAG failed exhaustive verification")
    return full


def _add_exact_local(report, table, num_inputs, max_local_ands):
    d_report = report["d_reduction"]
    if d_report["status"] == "constant-zero":
        full = make_xag(
            num_inputs, [], [affine(0, [])],
            metadata={
                "generator": "regular_reduce.sage",
                "construction": "constant zero",
                "minimum_and_count_proved": True,
                "verified_exhaustively": True,
            },
        )
        d_report["local_exact_synthesis"] = {
            "status": "constant-zero",
            "local_and_count": 0,
            "constructive_and_upper_bound": 0,
            "full_xag": full,
            "full_construction_global_optimality": "minimum follows from constant output",
        }
        return

    hull = d_report["_hull"]
    projection_autosymmetry = d_report["_projection_autosymmetry"]
    local_table = projection_autosymmetry["_quotient_table"]
    local_num_inputs = projection_autosymmetry["quotient_num_inputs"]
    if local_num_inputs > MAX_EXACT_LOCAL_INPUTS:
        raise ValueError(
            "--exact-local target has %d inputs; the safety limit is %d"
            % (local_num_inputs, MAX_EXACT_LOCAL_INPUTS)
        )
    budget = local_num_inputs if max_local_ands is None else int(max_local_ands)
    if budget < 0:
        raise ValueError("--max-local-ands must be non-negative")
    search = _load_exact_search()
    local_xag = search(
        local_num_inputs, [local_table], max_ands=budget, mode="full"
    )
    if local_xag is None:
        d_report["local_exact_synthesis"] = {
            "status": "unsat-within-budget",
            "target_num_inputs": local_num_inputs,
            "max_local_ands": budget,
            "constructive_and_upper_bound": None,
        }
        return

    original_projection_forms = hull["projection"]["input_affine_forms"]
    local_input_forms = _compose_forms(
        projection_autosymmetry["reduction_forms"],
        original_projection_forms,
    )
    full = _embed_local_xag(
        local_xag,
        num_inputs,
        local_input_forms,
        hull["membership_factors"],
        table,
    )
    local_count = int(local_xag["metrics"]["and_count"])
    codimension = int(hull["codimension"])
    d_report["local_exact_synthesis"] = {
        "status": "synthesized",
        "target": "autosymmetry quotient of f_A",
        "target_num_inputs": local_num_inputs,
        "target_truth_table": _table_string(local_table),
        "local_input_affine_forms_over_original_inputs": local_input_forms,
        "local_xag": local_xag,
        "local_and_count": local_count,
        "local_minimum_and_count_proved": True,
        "constructive_and_upper_bound": codimension + local_count,
        "bound_formula": "codimension(A) + local AND count",
        "full_xag": full,
        "full_xag_and_count_after_constant_folding": full["metrics"]["and_count"],
        "full_construction_global_optimality": "not claimed",
        "verified_exhaustively": True,
    }


def analyze(table, num_inputs, exact_local=False, max_local_ands=None):
    if num_inputs < 0 or len(table) != (1 << num_inputs):
        raise ValueError("truth table must have 2^num_inputs entries")
    if any(int(bit) not in (0, 1) for bit in table):
        raise ValueError("truth-table entries must be bits")
    if num_inputs > MAX_DEFAULT_INPUTS:
        raise ValueError(
            "truth table has %d inputs; the exhaustive safety limit is %d"
            % (num_inputs, MAX_DEFAULT_INPUTS)
        )
    table = [int(bit) for bit in table]
    autosymmetry = autosymmetry_reduce(table, num_inputs)
    d_reduction = d_reduce(table, num_inputs)
    report = {
        "format": REPORT_FORMAT,
        "version": REPORT_VERSION,
        "problem": {
            "num_inputs": num_inputs,
            "num_outputs": 1,
            "truth_table": _table_string(table),
            "truth_table_order": "index i has x[j] = (i >> j) & 1",
        },
        "autosymmetry": {
            key: value for key, value in autosymmetry.items()
            if not key.startswith("_")
        },
        "d_reduction": {
            key: value for key, value in d_reduction.items()
            if not key.startswith("_")
        },
    }
    # Retain private construction data only while optional synthesis runs.
    report["d_reduction"].update({
        key: value for key, value in d_reduction.items() if key.startswith("_")
    })
    if exact_local:
        _add_exact_local(report, table, num_inputs, max_local_ands)
    report["d_reduction"] = {
        key: value for key, value in report["d_reduction"].items()
        if not key.startswith("_")
    }
    return report


def _infer_num_inputs(length):
    if length <= 0 or length & (length - 1):
        raise ValueError("truth-table length must be a positive power of two")
    return length.bit_length() - 1


def _parse_table(text, num_inputs=None):
    raw = text.strip().replace("_", "").replace(",", "").replace(" ", "")
    if raw.startswith("0x"):
        if num_inputs is None:
            raise ValueError("--num-inputs is required for a hexadecimal table")
        size = 1 << int(num_inputs)
        value = int(raw, 16)
        if value >= (1 << size):
            raise ValueError("hexadecimal table does not fit 2^num_inputs bits")
        return int(num_inputs), [(value >> i) & 1 for i in range(size)]
    if not raw or any(bit not in "01" for bit in raw):
        raise ValueError("table must contain only binary digits")
    inferred = _infer_num_inputs(len(raw))
    n = inferred if num_inputs is None else int(num_inputs)
    if n != inferred:
        raise ValueError("table length disagrees with --num-inputs")
    return n, [int(bit) for bit in raw]


def _self_test():
    parity = [0, 1, 1, 0]
    auto = autosymmetry_reduce(parity, 2)
    assert auto["translation_invariance_subspace"]["dimension"] == 1
    assert auto["quotient_num_inputs"] == 1
    assert auto["quotient_truth_table"] == "01"

    x0_of_three = [(point >> 0) & 1 for point in range(8)]
    auto = autosymmetry_reduce(x0_of_three, 3)
    assert auto["translation_invariance_subspace"]["dimension"] == 2
    assert auto["quotient_num_inputs"] == 1

    table = [int(point in (0, 5, 6)) for point in range(8)]
    d_report = d_reduce(table, 3)
    hull = d_report["_hull"]
    assert hull["dimension"] == 2 and hull["codimension"] == 1
    assert hull["membership_and_count_exact"] == 0

    singleton = [0] * 7 + [1]
    singleton_hull = d_reduce(singleton, 3)["_hull"]
    assert singleton_hull["dimension"] == 0
    assert singleton_hull["membership_and_count_exact"] == 2

    zero = analyze([0] * 8, 3)
    assert zero["autosymmetry"]["quotient_num_inputs"] == 0
    assert zero["d_reduction"]["status"] == "constant-zero"
    one = analyze([1] * 8, 3)
    assert one["autosymmetry"]["quotient_num_inputs"] == 0
    assert one["d_reduction"]["affine_hull"]["codimension"] == 0

    combined_table = []
    for point in range(16):
        x1 = (point >> 1) & 1
        x2 = (point >> 2) & 1
        x3 = (point >> 3) & 1
        combined_table.append(int(not x3 and not (x1 and x2)))
    combined = d_reduce(combined_table, 4)
    assert combined["_hull"]["dimension"] == 3
    assert (
        combined["_projection_autosymmetry"]
        ["translation_invariance_subspace"]["dimension"] == 1
    )

    local = make_xag(
        2,
        [{"left": affine(0, [0]), "right": affine(0, [1])}],
        [affine(1, [2])],
    )
    full = _embed_local_xag(
        local,
        3,
        hull["projection"]["input_affine_forms"],
        hull["membership_factors"],
        table,
    )
    assert truth_tables(full) == [table]
    print("regular_reduce.sage: PASS")


def _main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--table", help="single-output truth bits in table-index order")
    parser.add_argument("--num-inputs", type=int, help="optional for a binary table; required for hex")
    parser.add_argument(
        "--exact-local", action="store_true",
        help="exactly synthesize the reduced local function and emit a lifted full XAG",
    )
    parser.add_argument(
        "--max-local-ands", type=int,
        help="exact-search budget; defaults to the reduced local input count",
    )
    parser.add_argument("--json", dest="json_path", help="also write the JSON report here")
    args = parser.parse_args(argv)
    if args.table is None:
        if any((args.num_inputs is not None, args.exact_local,
                args.max_local_ands is not None, args.json_path is not None)):
            parser.error("--table is required when options are supplied")
        try:
            _self_test()
            return 0
        except Exception as error:
            print("regular_reduce.sage: FAIL: %s" % error, file=sys.stderr)
            return 1
    if args.max_local_ands is not None and not args.exact_local:
        parser.error("--max-local-ands requires --exact-local")
    try:
        n, table = _parse_table(args.table, args.num_inputs)
        report = analyze(
            table, n, exact_local=args.exact_local,
            max_local_ands=args.max_local_ands,
        )
    except (ValueError, RuntimeError) as error:
        parser.error(str(error))
    rendered = json.dumps(report, indent=2, sort_keys=True, default=int)
    print(rendered)
    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    return 0


if os.path.basename(sys.argv[0]).startswith("regular_reduce.sage"):
    _status = int(_main(sys.argv[1:]))
    if _status:
        raise SystemExit(_status)
