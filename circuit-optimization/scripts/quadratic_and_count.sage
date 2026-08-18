#!/usr/bin/env sage
"""Polar-rank XAG construction for one quadratic GF(2) function.

The construction performs symplectic elimination on the polar matrix B_f,
emits rank(B_f)/2 XAG gates, and verifies the resulting truth table.

Truth-table index ``i`` uses ``x[j] = (i >> j) & 1``.
"""

import argparse
import os
import sys

from sage.all import GF, matrix
from sage.crypto.boolean_function import BooleanFunction

_cwd_scripts = os.path.join(os.getcwd(), "scripts")
if os.path.isdir(_cwd_scripts) and _cwd_scripts not in sys.path:
    sys.path.insert(0, _cwd_scripts)
try:
    from xag import affine, dumps_xag, make_xag, truth_tables
except ImportError:
    from scripts.xag import affine, dumps_xag, make_xag, truth_tables


def _infer_num_inputs(length):
    if length <= 0 or length & (length - 1):
        raise ValueError("truth-table length must be a positive power of two")
    return length.bit_length() - 1


def _truth_table(function, num_inputs=None):
    if isinstance(function, BooleanFunction) or hasattr(function, "truth_table"):
        bits = [int(bit) for bit in function.truth_table()]
        reported = int(function.nvariables())
        if num_inputs is not None and int(num_inputs) != reported:
            raise ValueError("num_inputs disagrees with BooleanFunction")
        n = reported
    else:
        bits = [int(bit) for bit in function]
        inferred = _infer_num_inputs(len(bits))
        n = inferred if num_inputs is None else int(num_inputs)
    if n < 0 or len(bits) != (1 << n):
        raise ValueError("truth table must have 2^num_inputs entries")
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("truth-table entries must be bits")
    return n, bits


def anf_coefficients(function, num_inputs=None):
    """Return ``(n, coefficients)`` indexed by ANF monomial support masks."""
    n, coefficients = _truth_table(function, num_inputs)
    coefficients = list(coefficients)
    for variable in range(n):
        bit = 1 << variable
        for support in range(1 << n):
            if support & bit:
                coefficients[support] = (
                    coefficients[support] + coefficients[support - bit]
                ) % 2
    return n, coefficients


def polar_matrix(function, num_inputs=None):
    """Return the polar matrix B_f, rejecting degree greater than two."""
    n, coefficients = anf_coefficients(function, num_inputs)
    high_degree = [
        support for support, coefficient in enumerate(coefficients)
        if coefficient and support.bit_count() > 2
    ]
    if high_degree:
        raise ValueError(
            "function is not quadratic; ANF has degree-%d term"
            % max(support.bit_count() for support in high_degree)
        )
    rows = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            coefficient = coefficients[(1 << i) | (1 << j)]
            rows[i][j] = rows[j][i] = coefficient
    return matrix(GF(2), rows)


def quadratic_and_count(function, num_inputs=None):
    """Return the rank(B_f)/2 factor count used by the construction."""
    rank = int(polar_matrix(function, num_inputs).rank())
    if rank % 2:
        raise AssertionError("an alternating matrix over GF(2) has even rank")
    return rank // 2


def _symplectic_factors(rows):
    """Write an alternating matrix as sum(a*b^T + b*a^T)."""
    residual = [list(map(int, row)) for row in rows]
    n = len(residual)
    factors = []
    while True:
        pivot = next(
            ((i, j) for i in range(n) for j in range(i + 1, n) if residual[i][j]),
            None,
        )
        if pivot is None:
            break
        p, q = pivot
        a = [residual[i][q] for i in range(n)]
        b = [residual[i][p] for i in range(n)]
        factors.append((a, b))
        for i in range(n):
            for j in range(n):
                residual[i][j] = (
                    residual[i][j] + (a[i] & b[j]) + (b[i] & a[j])
                ) % 2
        if any(residual[p]) or any(residual[q]):
            raise AssertionError("symplectic elimination failed to clear its pivot")
    return factors


def synthesize_quadratic(function, num_inputs=None):
    """Emit and exhaustively verify a polar-factorized XAG."""
    n, table = _truth_table(function, num_inputs)
    _, coefficients = anf_coefficients(table, n)
    polar = polar_matrix(table, n)
    factors = _symplectic_factors(polar.rows())
    expected = int(polar.rank()) // 2
    if len(factors) != expected:
        raise AssertionError("factor count does not match rank(B_f)/2")

    gates = []
    diagonal_correction = [0] * n
    for a, b in factors:
        gates.append({
            "left": affine(0, [i for i, bit in enumerate(a) if bit]),
            "right": affine(0, [i for i, bit in enumerate(b) if bit]),
        })
        for i in range(n):
            diagonal_correction[i] = (
                diagonal_correction[i] + (a[i] & b[i])
            ) % 2

    linear_terms = [
        i for i in range(n)
        if coefficients[1 << i] != diagonal_correction[i]
    ]
    linear_terms.extend(n + gate for gate in range(len(gates)))
    output = affine(coefficients[0], linear_terms)
    xag = make_xag(
        n, gates, [output],
        metadata={
            "construction": "quadratic-polar-rank",
            "polar_rank": int(polar.rank()),
            "verified_exhaustively": True,
        },
    )
    if truth_tables(xag) != [table]:
        raise AssertionError("emitted quadratic XAG failed exhaustive verification")
    return xag


def _parse_bits(text):
    raw = text.strip().replace("_", "").replace(",", "")
    if any(bit not in "01" for bit in raw):
        raise ValueError("table must contain only binary digits")
    bits = [int(bit) for bit in raw]
    _infer_num_inputs(len(bits))
    return bits


def _self_test():
    affine_table = [0, 1, 1, 0]
    affine_xag = synthesize_quadratic(BooleanFunction(affine_table))
    assert affine_xag["metrics"]["and_count"] == 0

    rank_four = [
        (((point >> 0) & 1) * ((point >> 1) & 1) +
         ((point >> 2) & 1) * ((point >> 3) & 1)) % 2
        for point in range(16)
    ]
    rank_four_xag = synthesize_quadratic(BooleanFunction(rank_four))
    assert quadratic_and_count(rank_four) == 2
    assert rank_four_xag["metrics"]["and_count"] == 2

    # This triangle has three ANF monomials but polar rank two, so one product
    # with a linear correction is enough.
    triangle = [
        ((((point >> 0) & 1) * ((point >> 1) & 1) +
          ((point >> 0) & 1) * ((point >> 2) & 1) +
          ((point >> 1) & 1) * ((point >> 2) & 1)) % 2)
        for point in range(8)
    ]
    triangle_xag = synthesize_quadratic(triangle)
    assert triangle_xag["metrics"]["and_count"] == 1
    assert truth_tables(triangle_xag) == [triangle]

    cubic = [
        ((point >> 0) & 1) * ((point >> 1) & 1) * ((point >> 2) & 1)
        for point in range(8)
    ]
    try:
        synthesize_quadratic(cubic)
        raise AssertionError("cubic input should be rejected")
    except ValueError as error:
        assert "not quadratic" in str(error)
    print("quadratic_and_count.sage: PASS")


def _main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--table", help="truth bits in table-index order")
    parser.add_argument("--json", dest="json_path", help="also write XAG JSON here")
    args = parser.parse_args(argv)
    if args.table is None:
        _self_test()
        return 0
    try:
        xag = synthesize_quadratic(_parse_bits(args.table))
    except ValueError as error:
        parser.error(str(error))
    rendered = dumps_xag(xag)
    print(rendered)
    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    return 0


if os.path.basename(sys.argv[0]).startswith("quadratic_and_count.sage"):
    _status = int(_main(sys.argv[1:]))
    if _status:
        raise SystemExit(_status)
