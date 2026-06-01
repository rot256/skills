#!/usr/bin/env sage
# Synthesize a SINGLE rank-1 (R1CS) constraint computing a boolean function, in Sage.
#
# Shape searched (output `o` lives in one multiplicand, coefficient 1):
#
#     (o + A(x)) * R(x) = O(x),    A, R, O affine in the boolean inputs x = (x0..x_{n-1})
#
# Solving for the output:  o = O/R - A.  So to compute target f on {0,1}^n we need
#     O = R*(f + A),   O affine,  R a UNIT (nonzero) on the whole cube.
#
# Key fact: once R is FIXED, the per-point conditions are LINEAR in the coefficients of
# A and O. So enumerate small INTEGER affine R that are units on the cube; for each,
# solve the resulting linear system EXACTLY over QQ with Sage's native linear algebra.
# Working over QQ (not a specific F_p) is deliberate: it yields small, prime-independent
# constants -- often integers, but small-denominator fractions are equally fine -- valid
# in EVERY field whose characteristic avoids a small finite set of primes (the values R
# takes on the cube and any coefficient denominators), i.e. all sufficiently large fields.
# That is the "char > bound" form the `clean` Lean proofs use.
# Every returned gadget is independently re-verified by recomputing o.
#
# A "NONE within grid" is NOT a proof of impossibility (the grid is bounded). For a
# rigorous impossibility proof use cvc5 / QF_FF (scripts/impossible.smt2, exact over a
# specific F_p) or a Groebner argument over QQ (scripts/cofactors.sage, all large char).
#
# Run:   sage scripts/synthesize.sage
# Lib:   load("scripts/synthesize.sage"); find(3, [0,1,1,0,1,0,0,1])   # parity

from itertools import product


def points(n):
    """All boolean points; index i is MSB-first: x[k] = (i >> (n-1-k)) & 1."""
    return [(i, [(i >> (n - 1 - k)) & 1 for k in range(n)]) for i in range(1 << n)]


def find(n, table, rng=range(-9, 10), const_rng=None):
    """Search for (A, R, O); return a dict of coefficient lists over QQ, or None.

    A = a[0..n-1] + a_const ; R = b[..] + b_const ; O = c[..] + c_const.
    Coefficients are exact rationals (valid in any large-enough field). A None result
    means "not found in this grid", NOT impossibility -- use impossible.smt2 / cvc5.
    """
    if len(table) != (1 << n):
        raise ValueError("table must have 2^n = %d entries, got %d" % (1 << n, len(table)))
    if any(t not in (0, 1) for t in table):
        raise ValueError("table entries must be 0/1")
    if const_rng is None:
        const_rng = rng
    pts = points(n)
    for bcoef in product(rng, repeat=n):
        for bconst in const_rng:
            Rv = [sum(bcoef[k] * x[k] for k in range(n)) + bconst for _, x in pts]
            if any(r == 0 for r in Rv):          # R must be a unit on the cube
                continue
            # unknowns: a[0..n-1], a_const, c[0..n-1], c_const  (A = a.x + a_const, O = c.x + c_const)
            # per point: R*(a.x + a_const) - (c.x + c_const) = -f*R
            rows, rhs = [], []
            for k, (_, x) in enumerate(pts):
                Rk = Rv[k]
                rows.append([Rk * x[j] for j in range(n)] + [Rk] + [-x[j] for j in range(n)] + [-1])
                rhs.append(-table[k] * Rk)
            try:
                sol = matrix(QQ, rows).solve_right(vector(QQ, rhs))
            except ValueError:                   # inconsistent system for this R
                continue
            a = list(sol[:n]); a_c = sol[n]
            c = list(sol[n + 1:2 * n + 1]); c_c = sol[2 * n + 1]
            # independent re-verification: o = O/R - A == table at every point
            ok = all(
                (sum(c[j] * x[j] for j in range(n)) + c_c) / Rv[k]
                - (sum(a[j] * x[j] for j in range(n)) + a_c) == table[k]
                for k, (_, x) in enumerate(pts)
            )
            if ok:
                return {"A": a + [a_c], "R": list(bcoef) + [bconst], "O": c + [c_c]}
    return None


def _fmt(coef, names):
    terms = ["%s*%s" % (coef[k], names[k]) for k in range(len(names))] + ["%s" % coef[-1]]
    return " + ".join(terms)


if __name__ == "__main__":
    n = 3
    names = ["a", "b", "c"]
    FUNCS = {
        "and3":         [0, 0, 0, 0, 0, 0, 0, 1],
        "or3":          [0, 1, 1, 1, 1, 1, 1, 1],
        "parity(xor3)": [0, 1, 1, 0, 1, 0, 0, 1],
        "majority":     [0, 0, 0, 1, 0, 1, 1, 1],
        "exactly_one":  [0, 1, 1, 0, 1, 0, 0, 0],
        "mux a?b:c":    [0, 1, 0, 1, 0, 0, 1, 1],
    }
    for name, t in FUNCS.items():
        g = find(n, t)
        if g is None:
            print("%-14s -> NONE within grid (use impossible.smt2 / cvc5 for a real proof)" % name)
        else:
            print("%-14s -> (o + %s) * (%s) = %s"
                  % (name, _fmt(g["A"], names), _fmt(g["R"], names), _fmt(g["O"], names)))
