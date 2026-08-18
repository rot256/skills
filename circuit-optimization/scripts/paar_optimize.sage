#!/usr/bin/env sage
"""Greedy Paar-style ANF factoring for XOR-AND graphs.

This is a heuristic, not an exact synthesizer.  Products are the primary cost;
XOR count is reported and can be enabled only as a final tie-breaker.

With no arguments the file runs deterministic self-tests.  Truth-table bit i
is the value at the little-endian input assignment i.
"""

import argparse
import itertools
import json
import operator
import os
import random
import sys

_cwd_scripts = os.path.join(os.getcwd(), "scripts")
if os.path.isdir(_cwd_scripts) and _cwd_scripts not in sys.path:
    sys.path.insert(0, _cwd_scripts)
try:
    from xag import affine, make_xag, save_xag, truth_tables, xag_metrics
except ImportError:
    from scripts.xag import affine, make_xag, save_xag, truth_tables, xag_metrics


def _toggle(poly, monomial):
    """XOR a monomial into an ANF represented as a set."""
    if monomial in poly:
        poly.remove(monomial)
    else:
        poly.add(monomial)


def truth_table_to_anf(table, num_inputs):
    size = 1 << num_inputs
    if len(table) != size or any(bit not in (0, 1) for bit in table):
        raise ValueError("truth table must contain exactly 2^num_inputs bits")
    coefficients = list(table)
    for bit in range(num_inputs):
        for mask in range(size):
            if mask & (1 << bit):
                coefficients[mask] = operator.xor(
                    coefficients[mask], coefficients[operator.xor(mask, 1 << bit)]
                )
    return {
        frozenset(i for i in range(num_inputs) if mask & (1 << i))
        for mask, coefficient in enumerate(coefficients)
        if coefficient
    }


def _pair_occurrences(polynomials):
    occurrences = {}
    for output_index, poly in enumerate(polynomials):
        for monomial in poly:
            for pair in itertools.combinations(sorted(monomial), 2):
                occurrences.setdefault(pair, []).append((output_index, monomial))
    return occurrences


def _replace_pair(polynomials, pair, replacement):
    result = [set(poly) for poly in polynomials]
    pair_set = frozenset(pair)
    for output_index, poly in enumerate(polynomials):
        affected = [monomial for monomial in poly if pair_set <= monomial]
        for monomial in affected:
            result[output_index].remove(monomial)
            rewritten = frozenset((monomial - pair_set) | {replacement})
            _toggle(result[output_index], rewritten)
    return result


def _anf_residual_cost(polynomials):
    # The estimate deliberately prices only nonlinear products.  It is an upper
    # bound because the final realization also shares identical chain products.
    return sum(max(0, len(monomial) - 1) for poly in polynomials for monomial in poly)


def _prune_xag(obj):
    """Drop gates not reachable from an output and compact signal IDs."""
    n = obj["num_inputs"]
    gates = obj["gates"]
    needed = set()
    stack = [term for out in obj["outputs"] for term in out["terms"] if term >= n]
    while stack:
        signal = stack.pop()
        gate_index = signal - n
        if gate_index in needed:
            continue
        needed.add(gate_index)
        gate = gates[gate_index]
        for side in (gate["left"], gate["right"]):
            stack.extend(term for term in side["terms"] if term >= n)

    remap = {old: new for new, old in enumerate(sorted(needed))}

    def map_form(form):
        terms = [term if term < n else n + remap[term - n] for term in form["terms"]]
        return affine(form["constant"], terms)

    compact_gates = []
    for old_index in sorted(needed):
        gate = gates[old_index]
        compact_gates.append({"left": map_form(gate["left"]), "right": map_form(gate["right"])})
    return make_xag(
        n,
        compact_gates,
        [map_form(out) for out in obj["outputs"]],
        metadata=obj.get("metadata"),
    )


def _realize_polynomials(polynomials, num_inputs, pair_gates, metadata=None):
    gates = []
    # Abstract pair-gate IDs use the same sequence as the eventual gate IDs.
    for left, right in pair_gates:
        gates.append({"left": affine(0, [left]), "right": affine(0, [right])})

    product_cache = {}

    def product_signal(left, right):
        key = tuple(sorted((left, right)))
        if key in product_cache:
            return product_cache[key]
        signal = num_inputs + len(gates)
        gates.append({"left": affine(0, [left]), "right": affine(0, [right])})
        product_cache[key] = signal
        return signal

    outputs = []
    for poly in polynomials:
        constant = int(frozenset() in poly)
        terms = []
        for monomial in sorted((m for m in poly if m), key=lambda m: (len(m), tuple(sorted(m)))):
            factors = sorted(monomial)
            signal = factors[0]
            for factor in factors[1:]:
                signal = product_signal(signal, factor)
            terms.append(signal)
        outputs.append(affine(constant, terms))
    return _prune_xag(make_xag(num_inputs, gates, outputs, metadata=metadata))


def _synthesize_once(tables, num_inputs, seed=0):
    num_inputs = int(num_inputs)
    seed = int(seed)
    polynomials = [truth_table_to_anf(table, num_inputs) for table in tables]
    initial_anf_products = _anf_residual_cost(polynomials)
    pair_gates = []
    rng = random.Random(seed)

    while True:
        occurrences = _pair_occurrences(polynomials)
        # Paar's transposition is useful only when a pair occurs at least twice:
        # one new AND then replaces two or more residual products.
        candidates = [pair for pair, uses in occurrences.items() if len(uses) >= 2]
        if not candidates:
            break
        scored = []
        replacement = num_inputs + len(pair_gates)
        current_cost = _anf_residual_cost(polynomials)
        for pair in candidates:
            rewritten = _replace_pair(polynomials, pair, replacement)
            gain = current_cost - (1 + _anf_residual_cost(rewritten))
            scored.append((gain, pair, rewritten))
        best_gain = max(item[0] for item in scored)
        if best_gain <= 0:
            break
        tied = [item for item in scored if item[0] == best_gain]
        # Sorting makes a seed reproducible across Python hash randomization.
        tied.sort(key=lambda item: item[1])
        chosen = tied[rng.randrange(len(tied))]
        _, pair, polynomials = chosen
        pair_gates.append(pair)

    metadata = {
        "generator": "paar_optimize.sage",
        "optimality": "heuristic; no minimum-AND certificate",
        "seed": seed,
        "initial_anf_product_upper_bound": int(initial_anf_products),
        "shared_pair_products": len(pair_gates),
    }
    return _realize_polynomials(polynomials, num_inputs, pair_gates, metadata)


def _random_invertible_rows(num_inputs, rng):
    num_inputs = int(num_inputs)
    rows = [int(1) << i for i in range(num_inputs)]
    if num_inputs == 0:
        return rows
    # Random elementary row operations retain invertibility and are cheaper than
    # rejection-sampling GL(n, 2).
    for _ in range(max(1, 4 * num_inputs * num_inputs)):
        operation = rng.randrange(3)
        i = rng.randrange(num_inputs)
        j = rng.randrange(num_inputs)
        if i == j:
            continue
        if operation == 0:
            rows[i] = operator.xor(rows[i], rows[j])
        else:
            rows[i], rows[j] = rows[j], rows[i]
    return rows


def _inverse_rows(rows, num_inputs):
    num_inputs = int(num_inputs)
    rows = [int(row) for row in rows]
    augmented = [rows[i] | (1 << (num_inputs + i)) for i in range(num_inputs)]
    for column in range(num_inputs):
        pivot = next(i for i in range(column, num_inputs) if augmented[i] & (1 << column))
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        for row in range(num_inputs):
            if row != column and augmented[row] & (1 << column):
                augmented[row] = operator.xor(augmented[row], augmented[column])
    return [(value >> num_inputs) & ((1 << num_inputs) - 1) for value in augmented]


def _matrix_vector(rows, vector):
    vector = int(vector)
    return sum((int(int(row) & vector).bit_count() & 1) << i for i, row in enumerate(rows))


def _transform_tables(tables, rows, offset, num_inputs):
    inverse = _inverse_rows(rows, num_inputs)
    transformed = [[] for _ in tables]
    for y in range(1 << num_inputs):
        x = _matrix_vector(inverse, operator.xor(y, offset))
        for output_index, table in enumerate(tables):
            transformed[output_index].append(table[x])
    return transformed


def _compose_input_affine(obj, rows, offset):
    n = obj["num_inputs"]
    aliases = [
        affine((offset >> i) & 1, [j for j in range(n) if rows[i] & (1 << j)])
        for i in range(n)
    ]

    def substitute(form):
        constant = form["constant"]
        terms = set()
        for term in form["terms"]:
            if term < n:
                source = aliases[term]
                constant = operator.xor(constant, source["constant"])
                for source_term in source["terms"]:
                    if source_term in terms:
                        terms.remove(source_term)
                    else:
                        terms.add(source_term)
            else:
                if term in terms:
                    terms.remove(term)
                else:
                    terms.add(term)
        return affine(constant, sorted(terms))

    gates = [
        {"left": substitute(gate["left"]), "right": substitute(gate["right"])}
        for gate in obj["gates"]
    ]
    metadata = dict(obj.get("metadata", {}))
    metadata["input_affine_rows"] = rows
    metadata["input_affine_offset"] = offset
    return _prune_xag(make_xag(n, gates, [substitute(out) for out in obj["outputs"]], metadata))


def optimize(tables, num_inputs, seed=0, affine_trials=0, xor_tiebreak=False):
    """Return a verified heuristic XAG for one or more truth tables.

    `affine_trials` counts additional seeded random affine input transforms; the
    identity trial is always included.  Selection minimizes ANDs, then depth,
    and only then XORs when explicitly requested.
    """
    num_inputs = int(num_inputs)
    seed = int(seed)
    affine_trials = int(affine_trials)
    expected = 1 << num_inputs
    if not tables or any(len(table) != expected for table in tables):
        raise ValueError("each truth table must have length 2^num_inputs")
    rng = random.Random(seed)
    candidates = [_synthesize_once(tables, num_inputs, seed)]
    for trial in range(affine_trials):
        rows = _random_invertible_rows(num_inputs, rng)
        offset = rng.randrange(1 << num_inputs)
        transformed = _transform_tables(tables, rows, offset, num_inputs)
        candidate = _synthesize_once(transformed, num_inputs, seed + trial + 1)
        candidates.append(_compose_input_affine(candidate, rows, offset))

    def cost(candidate):
        metrics = xag_metrics(candidate)
        base = (metrics["and_count"], metrics["and_depth"])
        return base + ((metrics["xor_count"],) if xor_tiebreak else ())

    best = min(candidates, key=cost)
    metadata = dict(best.get("metadata", {}))
    metadata.update({
        "affine_trials": affine_trials,
        "selection_cost": "and_count, and_depth" + (", xor_count" if xor_tiebreak else ""),
    })
    best["metadata"] = metadata
    # Exhaustive verification is intentionally unconditional: this is a small-
    # Boolean-function tool, and a heuristic should never weaken correctness.
    actual = truth_tables(best)
    if actual != [list(table) for table in tables]:
        raise AssertionError("internal error: synthesized XAG failed exhaustive verification")
    return best


def _parse_table(text, num_inputs):
    size = 1 << num_inputs
    if text.startswith("0x"):
        value = int(text, 16)
        if value >= (1 << size):
            raise ValueError("integer truth table does not fit 2^num_inputs bits")
        return [(value >> i) & 1 for i in range(size)]
    if text.startswith("0b"):
        value = int(text, 2)
        if value >= (1 << size):
            raise ValueError("integer truth table does not fit 2^num_inputs bits")
        return [(value >> i) & 1 for i in range(size)]
    bits = [int(bit) for bit in text.replace(",", "").replace("_", "")]
    if len(bits) != size or any(bit not in (0, 1) for bit in bits):
        raise ValueError("literal truth table must be 2^num_inputs zero/one characters")
    return bits


def self_test():
    xor2 = [0, 1, 1, 0]
    and2 = [0, 0, 0, 1]
    majority = [int(i.bit_count() >= 2) for i in range(8)]
    assert truth_tables(optimize([[1]], 0, affine_trials=2)) == [[1]]
    assert xag_metrics(optimize([xor2], 2))["and_count"] == 0
    assert xag_metrics(optimize([and2], 2))["and_count"] == 1
    assert xag_metrics(optimize([majority], 3))["and_count"] == 3

    shared = optimize([and2, and2], 2)
    assert xag_metrics(shared)["and_count"] == 1
    assert truth_tables(shared) == [and2, and2]

    # Affine preprocessing is seeded and must preserve the original function.
    first = optimize([majority], 3, seed=19, affine_trials=8)
    second = optimize([majority], 3, seed=19, affine_trials=8)
    assert first == second
    assert truth_tables(first) == [majority]
    print("PASS: paar_optimize.sage self-tests")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--num-inputs", type=int, required=True)
    parser.add_argument("--truth-table", action="append", required=True,
                        help="repeat for multiple outputs; hex is little-endian, literal bits are index order")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--affine-trials", type=int, default=0)
    parser.add_argument("--xor-tiebreak", action="store_true")
    parser.add_argument("--output", help="write JSON here; stdout when omitted")
    args = parser.parse_args(argv)
    tables = [_parse_table(text, args.num_inputs) for text in args.truth_table]
    result = optimize(tables, args.num_inputs, args.seed, args.affine_trials, args.xor_tiebreak)
    if args.output:
        save_xag(result, args.output)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if os.path.basename(sys.argv[0]).startswith("paar_optimize.sage"):
    if len(sys.argv) == 1:
        self_test()
    else:
        main()
