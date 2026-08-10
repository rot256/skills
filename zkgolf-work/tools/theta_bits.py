#!/usr/bin/env python3
"""
Keccak theta as a shortest linear program in the *real* cost model.

Cost model (read off Challenge notes in prompts_small/keccak-f1600.md):
    round score = 153600 + 48*h
where the 1600 target bits A'[x][y][b] are already paid for in the 153600 base
(one Xor3 row each) and h counts *helper* gates only -- gates whose output is
not a target.  Every gate, helper or target, is Xor3: z = u XOR v XOR w with
u,v,w each an already-materialised bit or a constant.  There is no lane
rotation primitive here: the whole thing is bit-level, and rot1 is just index
arithmetic on b.

Record: h = 640 = 320 column-slices x 2 helpers
        (t[x][b] = A[x][0][b]^A[x][1][b]^A[x][2][b],  C[x][b] = t^A[x][3][b]^A[x][4][b])

Structure that matters
----------------------
  T[x][y][b] = A[x][y][b] ^ C[x-1][b] ^ C[x+1][b-1]
Within one column-slice (x,b) the five targets differ by two raw bits, so once
ONE of them ("the seed") exists the other four are free target gates
  T[x][y'][b] = T[x][y][b] ^ A[x][y][b] ^ A[x][y'][b].
So only 320 seeds have to be constructed.

Let node n = (x,b) carry the 5 atoms of that column-slice, P_n their parity.
Seed of slice (z,b) needs P_{(z-1,b)} and P_{(z+1,b-1)}.  Viewing nodes as
vertices and slices as edges, every node has degree 2 and the graph is a
SINGLE 320-cycle: (x,b) -> (x+2,b-1) -> ... returns after lcm(5,64)... = 320
steps.  The rider atom of the edge leaving node n belongs to node n+128.
"""

import itertools
import json
import os
import random
import sys
import time

R = 5  # rows


def make_problem(ncols=5, w=64, rows=5):
    """Returns (natoms, atom_index, targets, slices).

    atom (x,y,b) -> index;  target[(x,y,b)] = bitmask over atoms
    """
    idx = {}
    n = 0
    for x in range(ncols):
        for y in range(rows):
            for b in range(w):
                idx[(x, y, b)] = n
                n += 1
    C = {}
    for x in range(ncols):
        for b in range(w):
            m = 0
            for y in range(rows):
                m |= 1 << idx[(x, y, b)]
            C[(x, b)] = m
    T = {}
    for x in range(ncols):
        for y in range(rows):
            for b in range(w):
                T[(x, y, b)] = ((1 << idx[(x, y, b)])
                                ^ C[((x - 1) % ncols, b)]
                                ^ C[((x + 1) % ncols, (b - 1) % w)])
    return n, idx, T, C


# ---------------------------------------------------------------------------
# reference check
# ---------------------------------------------------------------------------

def theta_ref(A, w=64):
    C = [[0] * w for _ in range(5)]
    for x in range(5):
        for b in range(w):
            v = 0
            for y in range(5):
                v ^= A[x][y][b]
            C[x][b] = v
    out = [[[0] * w for _ in range(5)] for _ in range(5)]
    for x in range(5):
        for y in range(5):
            for b in range(w):
                out[x][y][b] = (A[x][y][b] ^ C[(x - 1) % 5][b]
                                ^ C[(x + 1) % 5][(b - 1) % w])
    return out


def check_targets_against_reference(w=64, trials=50, seed=3):
    n, idx, T, C = make_problem(5, w, 5)
    rng = random.Random(seed)
    for _ in range(trials):
        A = [[[rng.getrandbits(1) for _ in range(w)] for _ in range(5)]
             for _ in range(5)]
        flat = [0] * n
        for x in range(5):
            for y in range(5):
                for b in range(w):
                    flat[idx[(x, y, b)]] = A[x][y][b]
        ref = theta_ref(A, w)
        for k, m in T.items():
            v = 0
            mm = m
            while mm:
                low = mm & -mm
                v ^= flat[low.bit_length() - 1]
                mm ^= low
            if v != ref[k[0]][k[1]][k[2]]:
                return False
    # also cross-check against the 64-bit-word reference
    def rotl64(a, r):
        r %= 64
        return ((a << r) | (a >> (64 - r))) & ((1 << 64) - 1) if r else a
    if w == 64:
        for _ in range(trials):
            Aw = [[rng.getrandbits(64) for _ in range(5)] for _ in range(5)]
            Cw = [Aw[x][0] ^ Aw[x][1] ^ Aw[x][2] ^ Aw[x][3] ^ Aw[x][4]
                  for x in range(5)]
            Dw = [Cw[(x - 1) % 5] ^ rotl64(Cw[(x + 1) % 5], 1) for x in range(5)]
            outw = [[Aw[x][y] ^ Dw[x] for y in range(5)] for x in range(5)]
            flat = [0] * n
            for x in range(5):
                for y in range(5):
                    for b in range(64):
                        flat[idx[(x, y, b)]] = (Aw[x][y] >> b) & 1
            for x in range(5):
                for y in range(5):
                    for b in range(64):
                        v = 0
                        mm = T[(x, y, b)]
                        while mm:
                            low = mm & -mm
                            v ^= flat[low.bit_length() - 1]
                            mm ^= low
                        if v != ((outw[x][y] >> b) & 1):
                            return False
    return True


# ---------------------------------------------------------------------------
# the record construction, in this cost model
# ---------------------------------------------------------------------------

def record_construction(w=64):
    """h = 640.  Returns (helpers, target_gates) as symbolic gate lists."""
    helpers = []
    tg = []
    for x in range(5):
        for b in range(w):
            helpers.append(("t[%d,%d]" % (x, b),
                            "A[%d,0,%d]" % (x, b),
                            "A[%d,1,%d]" % (x, b),
                            "A[%d,2,%d]" % (x, b)))
            helpers.append(("C[%d,%d]" % (x, b),
                            "t[%d,%d]" % (x, b),
                            "A[%d,3,%d]" % (x, b),
                            "A[%d,4,%d]" % (x, b)))
    for x in range(5):
        for y in range(5):
            for b in range(w):
                tg.append(("T[%d,%d,%d]" % (x, y, b),
                           "A[%d,%d,%d]" % (x, y, b),
                           "C[%d,%d]" % ((x - 1) % 5, b),
                           "C[%d,%d]" % ((x + 1) % 5, (b - 1) % w)))
    return helpers, tg


def eval_gatelist(helpers, tg, w=64, trials=20, seed=11):
    """Concrete verification against the reference theta."""
    rng = random.Random(seed)
    for _ in range(trials):
        A = [[[rng.getrandbits(1) for _ in range(w)] for _ in range(5)]
             for _ in range(5)]
        env = {}
        for x in range(5):
            for y in range(5):
                for b in range(w):
                    env["A[%d,%d,%d]" % (x, y, b)] = A[x][y][b]
        env["0"] = 0
        for g in list(helpers) + list(tg):
            env[g[0]] = env[g[1]] ^ env[g[2]] ^ env[g[3]]
        ref = theta_ref(A, w)
        for x in range(5):
            for y in range(5):
                for b in range(w):
                    if env["T[%d,%d,%d]" % (x, y, b)] != ref[x][y][b]:
                        return False
    return True


# ---------------------------------------------------------------------------
# generic helper-set feasibility: closure with FREE target gates
# ---------------------------------------------------------------------------

def closure(pool, targets):
    """pool: list of ints (materialised values).  targets: list of ints.
    A target is producible when it is a XOR of <=3 materialised values.
    Produced targets join the pool (they are free)."""
    S = set(pool)
    S.add(0)
    P = list(S)
    two = set()
    for i, a in enumerate(P):
        for b in P[i:]:
            two.add(a ^ b)
    done = set()
    changed = True
    while changed:
        changed = False
        for ti, t in enumerate(targets):
            if ti in done:
                continue
            ok = False
            for u in P:
                if (t ^ u) in two:
                    ok = True
                    break
            if ok:
                done.add(ti)
                if t not in S:
                    for a in list(P):
                        two.add(a ^ t)
                    S.add(t)
                    P.append(t)
                changed = True
    return done


def build_helpers(triples, natoms):
    src = [1 << i for i in range(natoms)]
    vals = []
    for (i, j, k) in triples:
        n = len(src)
        v = src[i % n] ^ src[j % n] ^ src[k % n]
        vals.append(v)
        src.append(v)
    return vals


def anneal_helpers(natoms, targets, nh, iters=30000, seed=0, T0=8.0, T1=0.3):
    """Simulated annealing on a set of nh helper gates; objective = #unresolved."""
    import math
    rng = random.Random(seed)
    tr = [tuple(rng.randrange(natoms + 3 * t) for _ in range(3))
          for t in range(nh)]

    def score(tr):
        vals = build_helpers(tr, natoms)
        pool = [1 << i for i in range(natoms)] + [v for v in vals if v]
        d = closure(pool, targets)
        return len(targets) - len(d)

    cur = score(tr)
    best, best_tr = cur, list(tr)
    if cur == 0:
        return 0, tr
    for it in range(iters):
        Temp = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        gi = rng.randrange(nh)
        si = rng.randrange(3)
        cand = [list(t) for t in tr]
        cand[gi][si] = rng.randrange(natoms + 3 * gi + 3)
        cand = [tuple(t) for t in cand]
        s = score(cand)
        if s <= cur or rng.random() < math.exp((cur - s) / Temp):
            tr, cur = cand, s
            if cur < best:
                best, best_tr = cur, list(tr)
            if best == 0:
                return 0, best_tr
    return best, best_tr


def analogue(ncols, w, nh, budget=60.0, seed=0, rows=5):
    """Search the (ncols, w) analogue for a solution with nh helpers."""
    natoms, idx, T, C = make_problem(ncols, w, rows)
    targets = list(T.values())
    t_end = time.time() + budget
    bestscore, besttr = None, None
    runs = 0
    while time.time() < t_end:
        runs += 1
        s, tr = anneal_helpers(natoms, targets, nh, iters=4000,
                               seed=seed * 7919 + runs)
        if bestscore is None or s < bestscore:
            bestscore, besttr = s, tr
        if s == 0:
            break
    return bestscore, besttr, runs, natoms, targets


def main():
    w = int(os.environ.get("W", 64))
    print("=" * 74)
    print("model check: bit-level target masks vs reference Keccak theta")
    ok = check_targets_against_reference(w=64, trials=30)
    print("  targets reproduce theta (bit and 64-bit-word reference):", ok)
    if not ok:
        sys.exit("model check failed")

    print("=" * 74)
    print("record construction in this cost model")
    hs, tg = record_construction(64)
    print("  helpers h =", len(hs), " target gates =", len(tg))
    print("  concrete verification vs reference theta:",
          eval_gatelist(hs, tg, 64, trials=8))
    print("  score = 153600 + 48*%d = %d" % (len(hs), 153600 + 48 * len(hs)))

    print("=" * 74)
    print("analogue searches (targets free, minimise helpers)")
    for (nc, ww, nh) in [(3, 1, 6), (3, 1, 5), (5, 1, 10), (5, 1, 9),
                         (5, 2, 20), (5, 2, 19)]:
        s, tr, runs, natoms, targets = analogue(
            nc, ww, nh, budget=float(os.environ.get("AN_BUDGET", 40)),
            seed=nc * 100 + ww)
        print("  ncols=%d w=%d helpers=%d : unresolved=%d/%d after %d runs %s"
              % (nc, ww, nh, s, len(targets), runs,
                 "<-- FEASIBLE" if s == 0 else ""))
        if s == 0 and nh in (5, 9, 19):
            vals = build_helpers(tr, natoms)
            print("      helper values (atom masks):",
                  [hex(v) for v in vals])
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "analogue_%d_%d_%d.json" % (nc, ww, nh)),
                      "w") as f:
                json.dump({"ncols": nc, "w": ww, "nh": nh,
                           "triples": [list(t) for t in tr],
                           "vals": vals}, f)


if __name__ == "__main__":
    main()
