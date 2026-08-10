#!/usr/bin/env python3
"""
Guided (simulated-annealing) search for the theta SLP in the 3-input-XOR basis.

Framing
-------
The 25 outputs A'[x,y] are 25 distinct non-input wires, so each needs its own
gate: h = 25 + g where g is the number of *auxiliary* gates.  The absorbed
schedule has g = 10 (the five column parities, 2 gates each).  This program
searches for g < 10.

An aux-gate set is feasible iff, starting from
    pool = {50 free atoms}  U  {aux gate values}  U  {their free rot1 variants}
the closure process "any target that is currently a 3-sum of the pool gets
emitted as one gate and joins the pool" resolves all 25 targets.  This closure
also covers schedules where one output is used as an operand of another.

Atom encoding: 50-bit int, bit i = s^0 * A[lane i], bit 25+i = s^1 * A[lane i].
rot1 of a wire is legal (stays inside the shift-{0,1} module) iff its s^1 block
is empty; then rot1(v) = v << 25.
"""

import json
import math
import os
import random
import sys
import time

import numpy as np

NL = 25
FULL = (1 << 50) - 1
LOW = (1 << 25) - 1


def lane(x, y):
    return 5 * x + y


def targets_and_D():
    C = [0] * 5
    for x in range(5):
        for y in range(5):
            C[x] ^= 1 << lane(x, y)
    D = []
    for x in range(5):
        c1 = C[(x - 1) % 5]              # shift 0
        c2 = C[(x + 1) % 5] << NL        # shift 1
        D.append(c1 ^ c2)
    T = []
    keys = []
    for x in range(5):
        for y in range(5):
            T.append((1 << lane(x, y)) ^ D[x])
            keys.append((x, y))
    return T, keys, C, D


ATOMS = [1 << i for i in range(50)]


def rot_ok(v):
    return (v >> NL) == 0


def build_pool(triples):
    """triples: list of (i,j,k) indices into the growing source list."""
    src = list(ATOMS)
    vals = []
    for (i, j, k) in triples:
        n = len(src)
        v = src[i % n] ^ src[j % n] ^ src[k % n]
        vals.append(v)
        src.append(v)
        if v and rot_ok(v):
            src.append(v << NL)
    return src, vals


def closure_resolved(pool_list, targets):
    """How many targets get resolved by iterated 3-sum closure."""
    S1 = set(pool_list)
    S1.add(0)
    P = list(S1)
    set2 = set()
    for a in P:
        for b in P:
            set2.add(a ^ b)
    unres = list(range(len(targets)))
    resolved = []
    changed = True
    while changed and unres:
        changed = False
        for ti in list(unres):
            T = targets[ti]
            hit = False
            for u in P:
                if (T ^ u) in set2:
                    hit = True
                    break
            if hit:
                resolved.append(ti)
                unres.remove(ti)
                if T not in S1:
                    for a in list(P):
                        set2.add(a ^ T)
                    S1.add(T)
                    P.append(T)
                    set2.add(T)
                changed = True
    return resolved, unres


def popcnt_arr(a):
    return np.bitwise_count(a)


def smooth_score(pool_list, targets, unres_idx):
    """sum over unresolved targets of min_{s in 2-sums(pool)} popcount(T ^ s)."""
    P = np.array(sorted(set(pool_list) | {0}), dtype=np.uint64)
    s2 = np.bitwise_xor(P[:, None], P[None, :]).ravel()
    s2 = np.unique(s2)
    tot = 0
    for ti in unres_idx:
        T = np.uint64(targets[ti])
        tot += int(popcnt_arr(np.bitwise_xor(s2, T)).min())
    return tot


def evaluate(triples, targets):
    src, vals = build_pool(triples)
    pool = [v for v in src if v]
    res, unres = closure_resolved(pool, targets)
    if not unres:
        return 0.0, len(res), (src, vals)
    sm = smooth_score(pool, targets, unres)
    return 1000.0 * len(unres) + sm, len(res), (src, vals)


def witness10():
    """The g=10 absorbed schedule, as triples of source indices."""
    tr = []
    src = list(ATOMS)
    for x in range(5):
        e = (1 << lane(x, 0)) | (1 << lane(x, 1)) | (1 << lane(x, 2))
        c = e | (1 << lane(x, 3)) | (1 << lane(x, 4))
        tr.append((src.index(1 << lane(x, 0)), src.index(1 << lane(x, 1)),
                   src.index(1 << lane(x, 2))))
        src.append(e)
        src.append(e << NL)
        ie = len(src) - 2
        tr.append((ie, src.index(1 << lane(x, 3)), src.index(1 << lane(x, 4))))
        src.append(c)
        src.append(c << NL)
    return tr


def seeded_start(g, rng):
    """Drop (10-g) gates from the g=10 witness and repair indices."""
    tr = witness10()
    keep = sorted(rng.sample(range(10), g))
    out = []
    for t in keep:
        out.append(tuple(i % (50 + 3 * len(out) + 1) for i in tr[t]))
    return out


def anneal(g, targets, iters=20000, seed=0, T0=60.0, T1=0.5, verbose=False,
           seeded=False):
    rng = random.Random(seed)
    triples = []
    n = 50
    if seeded and g <= 10:
        triples = seeded_start(g, rng)
    else:
        for t in range(g):
            triples.append(tuple(rng.randrange(n + 3 * t) for _ in range(3)))
    cur, nres, _ = evaluate(triples, targets)
    best, best_tr = cur, list(triples)
    for it in range(iters):
        Temp = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        gi = rng.randrange(g)
        si = rng.randrange(3)
        cand = [list(t) for t in triples]
        cand[gi][si] = rng.randrange(50 + 3 * gi + 3)
        cand = [tuple(t) for t in cand]
        newv, nres, _ = evaluate(cand, targets)
        if newv <= cur or rng.random() < math.exp((cur - newv) / Temp):
            triples, cur = cand, newv
            if cur < best:
                best, best_tr = cur, list(triples)
                if verbose:
                    print("    it=%d best=%.1f" % (it, best))
            if best == 0.0:
                return best, best_tr
    return best, best_tr


def main():
    targets, keys, C, D = targets_and_D()
    print("targets:", len(targets), "distinct:", len(set(targets)))
    print("D atom-weights:", [bin(d).count("1") for d in D])

    # sanity: the known g=10 witness (five column parities, 2 gates each)
    tr = []
    src = list(ATOMS)
    for x in range(5):
        e = (1 << lane(x, 0)) | (1 << lane(x, 1)) | (1 << lane(x, 2))
        c = e | (1 << lane(x, 3)) | (1 << lane(x, 4))
        i0 = src.index(1 << lane(x, 0))
        i1 = src.index(1 << lane(x, 1))
        i2 = src.index(1 << lane(x, 2))
        tr.append((i0, i1, i2))
        src.append(e)
        src.append(e << NL)
        ie = len(src) - 2
        tr.append((ie, src.index(1 << lane(x, 3)), src.index(1 << lane(x, 4))))
        src.append(c)
        src.append(c << NL)
    val, nres, _ = evaluate(tr, targets)
    print("witness g=10: objective=%.1f resolved=%d/25  (0.0 == feasible)"
          % (val, nres))

    budget = float(os.environ.get("ANNEAL_BUDGET", 240))
    results = {}
    for g in (9, 8, 7):
        t_end = time.time() + budget
        bestv, bestres, besttr = None, -1, None
        run = 0
        while time.time() < t_end:
            run += 1
            v, tr2 = anneal(g, targets, iters=6000, seed=1000 * g + run,
                            seeded=(run % 2 == 0))
            val, nres, _ = evaluate(tr2, targets)
            if bestv is None or val < bestv:
                bestv, bestres, besttr = val, nres, tr2
            if bestv == 0.0:
                break
        print("g=%d: %d annealing runs, best objective=%.1f, "
              "max targets resolved=%d/25 -> %s"
              % (g, run, bestv, bestres,
                 "FEASIBLE (h=%d)" % (25 + g) if bestv == 0.0 else "infeasible"))
        results[g] = (bestv, bestres, besttr)
        if bestv == 0.0:
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "anneal_hit_g%d.json" % g), "w") as f:
                json.dump({"g": g, "triples": [list(t) for t in besttr]}, f)
            break
    return results


if __name__ == "__main__":
    main()
