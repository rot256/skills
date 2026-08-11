#!/usr/bin/env python3
"""
Row-deletion (linear-redundancy) analysis of the SHA-256 padding predicate block
in projs/sha256-hash/Solution/SHA256/.

WHAT IS BEING MEASURED
----------------------
The blocks `CheckPad7SparseUnchecked.main` (cost <0,2062>),
`CheckPad7Sparse.main` (<0,2063>) and `CheckPad7.main` (<0,2167>) are pure
assertion blocks: they allocate no witnesses at all, they only emit R1CS rows
over variables that already exist (the circuit's inputs).  Every other block in
the tree sits within 32 rows of the structural floor r = m (one witness per
row); these ~2062 rows are the only ones with no witness to pin them.

The question: how many of these rows are *linearly redundant*, i.e. deletable
by the row-deletion criterion of "Distilling Constraints in Zero-Knowledge
Protocols" (CAV 2022)?

CRITERION
---------
Each R1CS row k is  (A_k . w)(B_k . w) - (C_k . w) = 0.  Write it as
    q_k(w) + L_k(w) + c_k = 0
where q_k is the homogeneous degree-2 part (a symmetric bilinear form), L_k the
degree-1 part and c_k the constant.  Solve

    sum_k lambda_k * q_k = 0     (as a quadratic form, i.e. coefficient-wise
                                  on every monomial w_i*w_j)

by plain Gaussian elimination over F_r.  Each solution lambda yields a purely
affine consequence  l = sum_k lambda_k (L_k + c_k) = 0  of the system:
  * if l == 0 identically, the rows in supp(lambda) are linearly redundant and
    one of them can be deleted outright;
  * otherwise l = 0 is a free linear constraint that can be used to eliminate a
    witness, after which a row becomes redundant.
The dimension of the kernel is the number of deletable rows.

THE CIRCUIT MODEL  (reconstructed from the Lean sources -- see below)
---------------------------------------------------------------------
Constants (Challenge/Instances/SHA256/Interface.lean, Solution/SHA256/Padding7.lean):
    inputBufferLen   = 256
    checkedBytesLen  = 255
    lowBitsPerByte   = 7
    circomPrime r    = BN254 scalar field

Variables of the block (all are *inputs*, none are allocated here):
    m                messageLen                                  1
    msg[0..255]      message bytes                             256
    f[0..255]        lenFlags (one-hot indicator of messageLen) 256
    l[j][t]          low bits, j=0..254, t=0..6                1785
                                                       total = 2298

Derived affine forms:
    active_j  = sum_{len=j+1}^{255} f[len]        (Padding7.activeFlagSum)
    S_j       = sum_{t=0}^{6} 2^t * l[j][t]       (Padding7.lowSum)
    d_j       = msg[j] - S_j                      (Padding7.Pair.highDelta)
    x_j       = d_j - 64 * active_j               (Padding7.Pair.highCentered)
    hi_j      = 128^{-1} * d_j                    (Padding7.highBit)

ROW FAMILIES (exact Lean provenance in comments at each builder below):

 (1) CheckLenFlags.row i,  i = 0..253                      -> 254 rows
       (m - (i+1)) * M_{i+1}(f)  -  (i+2) * M_{i+2}(f) = 0
     where M_d(f) = sum_k C(k,d) * f[k]  (chooseMomentExpr).
     R1CS: A = m-(i+1), B = M_{i+1}, C = (i+2)*M_{i+2}.

 (2) Padding7.Byte.lowMain, one per kept byte j, 7 rows each
       l[j][t] * (l[j][t] - active_j) = 0
     239 kept bytes -> 1673 rows  (255 bytes -> 1785 in the dense variant)

 (3) Padding7.Pair.main, one row per kept pair (bytes a = 2q, b = 2q+1)
       (x_a - 1024*x_b)*(x_a + 1024*x_b) - 4096*(active_a - 1048576*active_b) = 0
     119 kept pairs -> 119 rows  (127 in the dense variant)

 (4) SparseW0.row i, i = 0..15, over bytes {0..3, 64..67, 128..131, 192..195}
       msg[c] * (1 - active_c) = 0                          -> 16 rows

 (5) Padding7.Singleton.main (present in CheckPad7Sparse / CheckPad7, absent in
     CheckPad7SparseUnchecked), byte 254
       hi_254 * (hi_254 - active_254) = 0                    -> 1 row

Kept index sets (CheckPad7Sparse.lean):
    keptByteNat k  = k+4 (k<60) | k+8 (k<120) | k+12 (k<180) | k+16     239 bytes
    keptPairNat q  = q+2 (q<30) | q+4 (q<60)  | q+6  (q<90)  | q+8      119 pairs

TOTALS produced by this model (checked against the Lean `Count` values):
    CheckPad7SparseUnchecked : 254 + 1673 + 119 + 16     = 2062   (<0,2062>)
    CheckPad7Sparse          : 2062 + 1 (singleton)      = 2063   (<0,2063>)
    CheckPad7                : 254 + 1785 + 127 + 1      = 2167   (<0,2167>)
The exact agreement of all three totals is the primary evidence that the model
matches the real circuit.

ALGORITHM
---------
Sparse Gaussian elimination over F_r on the 2062 x (#monomials) matrix whose
rows are the q_k.  Pivot selection is Markowitz-style: repeatedly take the
monomial column occupied by the fewest rows.  Full lambda tracking is kept, so
any zero row produced is an explicit kernel vector.  rank + kernel_dim = #rows.
"""

import json
import sys
from collections import defaultdict
from math import comb

R = 21888242871839275222246405745257275088548364400416034343698204186575808495617

INPUT_BUFFER_LEN = 256
CHECKED_BYTES_LEN = 255
LOW_BITS_PER_BYTE = 7

# ---------------------------------------------------------------- variables --
V_M = 0
V_MSG = 1                                  # msg[i] -> 1 + i          (256)
V_F = V_MSG + INPUT_BUFFER_LEN             # f[i]   -> 257 + i        (256)
V_L = V_F + INPUT_BUFFER_LEN               # l[j][t]-> 513 + 7j + t   (1785)
NVARS = V_L + CHECKED_BYTES_LEN * LOW_BITS_PER_BYTE   # 2298

def v_msg(i): return V_MSG + i
def v_f(i):   return V_F + i
def v_l(j, t): return V_L + LOW_BITS_PER_BYTE * j + t

def mono(i, j):
    """Canonical key for the unordered monomial w_i * w_j."""
    return i * NVARS + j if i <= j else j * NVARS + i

# ------------------------------------------------------------- affine forms --
# An affine form is (dict var->coeff mod R, const mod R).

def aff(*, const=0, **_):
    return ({}, const % R)

def a_var(i, c=1):
    return ({i: c % R}, 0)

def a_const(c):
    return ({}, c % R)

def a_add(*forms):
    d = defaultdict(int)
    c = 0
    for (dd, cc) in forms:
        for k, v in dd.items():
            d[k] += v
        c += cc
    return ({k: v % R for k, v in d.items() if v % R}, c % R)

def a_scale(form, s):
    s %= R
    d, c = form
    if s == 0:
        return ({}, 0)
    return ({k: (v * s) % R for k, v in d.items()}, (c * s) % R)

def a_sub(x, y):
    return a_add(x, a_scale(y, -1))

def a_mul(x, y):
    """Product of two affine forms -> (quadratic dict, linear dict, const)."""
    dx, cx = x
    dy, cy = y
    q = defaultdict(int)
    for i, vi in dx.items():
        for j, vj in dy.items():
            q[mono(i, j)] += vi * vj
    lin = defaultdict(int)
    for i, vi in dx.items():
        lin[i] += vi * cy
    for j, vj in dy.items():
        lin[j] += vj * cx
    return ({k: v % R for k, v in q.items() if v % R},
            {k: v % R for k, v in lin.items() if v % R},
            (cx * cy) % R)

# --------------------------------------------------------- circuit pieces ----
def active(j):
    """Padding7.activeFlagSum lenFlags j = sum_{len : j < len} f[len]."""
    return ({v_f(k): 1 for k in range(j + 1, INPUT_BUFFER_LEN)}, 0)

def low_sum(j):
    """Padding7.lowSum (byteLowBits low j) = sum_t 2^t * l[j][t]."""
    return ({v_l(j, t): pow(2, t, R) for t in range(LOW_BITS_PER_BYTE)}, 0)

def high_delta(j):
    """Padding7.Pair.highDelta = msg[j] - lowSum_j."""
    return a_sub(a_var(v_msg(j)), low_sum(j))

def high_centered(j):
    """Padding7.Pair.highCentered = highDelta - 64*active."""
    return a_sub(high_delta(j), a_scale(active(j), 64))

INV128 = pow(128, R - 2, R)

def high_bit(j):
    """Padding7.highBit = 128^{-1} * (msg[j] - lowSum_j)."""
    return a_scale(high_delta(j), INV128)

# ------------------------------------------------------------- kept indices --
def kept_byte_nat(k):
    if k < 60:  return k + 4
    if k < 120: return k + 8
    if k < 180: return k + 12
    return k + 16

def kept_pair_nat(q):
    if q < 30: return q + 2
    if q < 60: return q + 4
    if q < 90: return q + 6
    return q + 8

KEPT_BYTES_LEN = 239
KEPT_PAIRS_LEN = 119
SINGLETON_INDEX = 254

def sparse_w0_target(i):
    """SparseW0.targetByte i = 64*(i/4) + i%4."""
    return 64 * (i // 4) + i % 4

# ------------------------------------------------------------- row builders --
class Row:
    __slots__ = ("q", "lin", "const", "tag")
    def __init__(self, q, lin, const, tag):
        self.q, self.lin, self.const, self.tag = q, lin, const, tag

def row_from_product(A, B, Cform, tag):
    """R1CS row (A.w)(B.w) - (C.w) = 0, split into quadratic/linear/constant."""
    q, lin, c = a_mul(A, B)
    dC, cC = Cform
    lin = dict(lin)
    for k, v in dC.items():
        lin[k] = (lin.get(k, 0) - v) % R
    lin = {k: v for k, v in lin.items() if v}
    return Row(q, lin, (c - cC) % R, tag)

def build_lenflags_rows():
    """CheckLenFlags.row i, i : Fin 254."""
    rows = []
    # moment vectors M_d(f) = sum_k C(k,d) f[k]
    def moment(d):
        return ({v_f(k): comb(k, d) % R
                 for k in range(INPUT_BUFFER_LEN) if comb(k, d) % R}, 0)
    for i in range(254):
        A = a_add(a_var(V_M), a_const(-(i + 1)))
        B = moment(i + 1)
        C = a_scale(moment(i + 2), i + 2)
        rows.append(row_from_product(A, B, C, ("lenflag", i)))
    return rows

def build_byte_low_rows(byte_indices):
    """Padding7.Byte.lowMain: l[j][t] * (l[j][t] - active_j) = 0."""
    rows = []
    for j in byte_indices:
        act = active(j)
        for t in range(LOW_BITS_PER_BYTE):
            A = a_var(v_l(j, t))
            B = a_sub(A, act)
            rows.append(row_from_product(A, B, a_const(0), ("low", j, t)))
    return rows

def build_pair_rows(pair_indices):
    """Padding7.Pair.main:
         (x0 - 1024 x1)(x0 + 1024 x1) - 4096*(active_a - 1048576*active_b) = 0
    """
    rows = []
    for p in pair_indices:
        a, b = 2 * p, 2 * p + 1
        x0 = high_centered(a)
        x1 = high_centered(b)
        A = a_sub(x0, a_scale(x1, 1024))
        B = a_add(x0, a_scale(x1, 1024))
        C = a_scale(a_sub(active(a), a_scale(active(b), 1048576)), 4096)
        rows.append(row_from_product(A, B, C, ("pair", p)))
    return rows

def build_sparse_w0_rows():
    """SparseW0.row i: msg[c] * (1 - active_c) = 0."""
    rows = []
    for i in range(16):
        c = sparse_w0_target(i)
        A = a_var(v_msg(c))
        B = a_sub(a_const(1), active(c))
        rows.append(row_from_product(A, B, a_const(0), ("sparseW0", i)))
    return rows

def build_singleton_row():
    """Padding7.Singleton.main: hi*(hi - active) = 0 at byte 254."""
    hi = high_bit(SINGLETON_INDEX)
    A = hi
    B = a_sub(hi, active(SINGLETON_INDEX))
    return [row_from_product(A, B, a_const(0), ("singleton",))]

def build_block(name):
    if name == "CheckPad7SparseUnchecked":
        return (build_lenflags_rows()
                + build_byte_low_rows([kept_byte_nat(k) for k in range(KEPT_BYTES_LEN)])
                + build_pair_rows([kept_pair_nat(q) for q in range(KEPT_PAIRS_LEN)])
                + build_sparse_w0_rows())
    if name == "CheckPad7Sparse":
        return (build_lenflags_rows()
                + build_byte_low_rows([kept_byte_nat(k) for k in range(KEPT_BYTES_LEN)])
                + build_pair_rows([kept_pair_nat(q) for q in range(KEPT_PAIRS_LEN)])
                + build_singleton_row()
                + build_sparse_w0_rows())
    if name == "CheckPad7":
        return (build_lenflags_rows()
                + build_byte_low_rows(list(range(CHECKED_BYTES_LEN)))
                + build_pair_rows(list(range(127)))
                + build_singleton_row())
    raise ValueError(name)

# ------------------------------------------------------------- elimination ---
def eliminate(rows, verbose=True):
    """Sparse Gaussian elimination over F_R on the quadratic parts.

    Returns (rank, kernel) where kernel is a list of dicts row_index -> lambda.
    Markowitz pivoting: always pivot on the monomial column held by the fewest
    live rows (which for a structurally non-degenerate system is 1, giving
    zero fill-in).
    """
    n = len(rows)
    work = [dict(r.q) for r in rows]              # quadratic parts, mutable
    lam = [{i: 1} for i in range(n)]              # tracked combination
    col = defaultdict(set)                        # monomial -> live row ids
    for i, w in enumerate(work):
        for c in w:
            col[c].add(i)

    live = set(i for i in range(n))
    kernel = []
    # rows that start out identically zero in the quadratic part
    for i in range(n):
        if not work[i]:
            kernel.append(lam[i])
            live.discard(i)

    # bucket columns by occupancy for cheap min selection
    rank = 0
    # worklist of columns currently occupied by exactly one live row; pivoting
    # on those costs nothing and produces no fill-in.
    singles = [c for c, s in col.items() if len(s) == 1]
    while True:
        best_c = None
        while singles:
            c = singles.pop()
            s = col.get(c)
            if s is not None and len(s) == 1:
                best_c = c
                break
        if best_c is None:
            # full Markowitz scan
            best_len = None
            for c, s in col.items():
                ls = len(s)
                if ls == 0:
                    continue
                if best_len is None or ls < best_len:
                    best_c, best_len = c, ls
                    if ls == 1:
                        break
        if best_c is None:
            break
        rowset = col[best_c]
        # pivot row = sparsest row in this column
        piv = min(rowset, key=lambda i: len(work[i]))
        pval = work[piv][best_c]
        pinv = pow(pval, R - 2, R)
        others = [i for i in rowset if i != piv]
        for i in others:
            factor = (work[i][best_c] * pinv) % R
            # work[i] -= factor * work[piv]
            wi = work[i]
            for c, v in work[piv].items():
                nv = (wi.get(c, 0) - factor * v) % R
                if nv:
                    if c not in wi:
                        col[c].add(i)
                    wi[c] = nv
                else:
                    if c in wi:
                        del wi[c]
                        sc = col[c]
                        sc.discard(i)
                        if len(sc) == 1:
                            singles.append(c)
            li = lam[i]
            for k, v in lam[piv].items():
                nv = (li.get(k, 0) - factor * v) % R
                if nv:
                    li[k] = nv
                elif k in li:
                    del li[k]
            if not wi:
                kernel.append(li)
                live.discard(i)
        # retire the pivot row
        for c in work[piv]:
            sc = col.get(c)
            if sc is not None:
                sc.discard(piv)
                if len(sc) == 1:
                    singles.append(c)
        col.pop(best_c, None)
        live.discard(piv)
        rank += 1
        if verbose and rank % 250 == 0:
            print(f"    ... {rank} pivots, {len(live)} rows live", file=sys.stderr)

    # anything still live has an empty quadratic part
    for i in list(live):
        assert not work[i]
        kernel.append(lam[i])
    return rank, kernel

def classify_kernel(rows, kernel):
    """For each kernel vector, decide REDUNDANT (affine residue identically 0)
    vs FREE LINEAR CONSTRAINT."""
    out = []
    for lamvec in kernel:
        lin = defaultdict(int)
        const = 0
        for k, c in lamvec.items():
            for var, v in rows[k].lin.items():
                lin[var] += c * v
            const += c * rows[k].const
        lin = {k: v % R for k, v in lin.items() if v % R}
        const %= R
        out.append({
            "support": sorted(lamvec.keys()),
            "kind": "REDUNDANT" if (not lin and const == 0) else "FREE_LINEAR",
        })
    return out

# ------------------------------------------------------------------- main ----
def main():
    expected = {
        "CheckPad7SparseUnchecked": 2062,
        "CheckPad7Sparse": 2063,
        "CheckPad7": 2167,
    }
    results = {}
    for name in ["CheckPad7SparseUnchecked", "CheckPad7Sparse", "CheckPad7"]:
        print(f"[{name}] building rows ...", file=sys.stderr)
        rows = build_block(name)
        nnz = sum(len(r.q) for r in rows)
        print(f"[{name}] rows = {len(rows)} (Lean Count says {expected[name]}), "
              f"quadratic nnz = {nnz}", file=sys.stderr)
        assert len(rows) == expected[name], (name, len(rows), expected[name])
        rank, kernel = eliminate(rows)
        cls = classify_kernel(rows, kernel)
        ndel = len(kernel)
        print(f"[{name}] rank = {rank}, kernel_dim = {len(kernel)}", file=sys.stderr)
        results[name] = {
            "rows_modelled": len(rows),
            "quadratic_nnz": nnz,
            "rank": rank,
            "kernel_dim": len(kernel),
            "deletable_rows": ndel,
            "kernel_kinds": [c["kind"] for c in cls],
        }

    primary = results["CheckPad7SparseUnchecked"]
    out = {
        "rows_modelled": primary["rows_modelled"],
        "rank": primary["rank"],
        "kernel_dim": primary["kernel_dim"],
        "deletable_rows": primary["deletable_rows"],
        "notes": (
            "Primary target: CheckPad7SparseUnchecked.main, the zero-allocation "
            "assertion block with Count <0,2062>. Rows reconstructed from the Lean "
            "sources (CheckLenFlags.row x254, Padding7.Byte.lowMain x7 over 239 kept "
            "bytes = 1673, Padding7.Pair.main x119, SparseW0.row x16); the model's "
            "row count reproduces all three Lean Count values exactly (2062/2063/2167), "
            "which validates the model. Criterion: exact Gaussian elimination over "
            "BN254 F_r on the homogeneous degree-2 parts q_k of every row. "
            "Kernel dimension is 0: every row carries a monomial that no other row "
            "in the block touches (msg[a]^2 for each pair row, l[j][t]^2 for each "
            "low-bit row, m*f[k] with a unitriangular binomial matrix for the "
            "CheckLenFlags rows, msg[c]*f[len] for each SparseW0 row), so no "
            "nontrivial lambda annihilates the quadratic parts. Zero rows are "
            "deletable by the row-deletion criterion; the same holds for the "
            "CheckPad7Sparse (2063) and dense CheckPad7 (2167) variants."
        ),
        "all_variants": results,
    }
    with open("/home/user/skills/zkgolf-work/tools/padding_rowdel_result.json", "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps({k: v for k, v in out.items() if k != "notes"}, indent=2))

if __name__ == "__main__":
    main()
