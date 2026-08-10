#!/usr/bin/env python3
"""
Decisive experiment: take the record's 2-helpers-per-column-slice construction
on a small but structurally faithful analogue of Keccak theta, DELETE one
helper, and search for a repair.  If a repair exists on an analogue whose
node-graph is a single cycle (as the real w=64 instance is), it ports.

Cost model: target gates are free (paid for in the 153600 base); helper gates
cost 1.  Every gate is a 3-input XOR of already-materialised bits.

Helpers may use atoms, earlier helpers, AND already-produced targets (staged),
so the "rider through a target" mechanism is inside the search space.
"""

import itertools
import json
import math
import os
import random
import sys
import time


def make_problem(ncols, w, rows=5):
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
    T = []
    tkey = []
    for x in range(ncols):
        for y in range(rows):
            for b in range(w):
                T.append((1 << idx[(x, y, b)])
                         ^ C[((x - 1) % ncols, b)]
                         ^ C[((x + 1) % ncols, (b - 1) % w)])
                tkey.append((x, y, b))
    return n, idx, C, T, tkey


def node_cycle(ncols, w):
    """The node graph (x,b) -- (x+2,b-1); returns its cycle decomposition."""
    nodes = [(x, b) for x in range(ncols) for b in range(w)]
    seen = set()
    cycles = []
    for s in nodes:
        if s in seen:
            continue
        cyc = []
        cur = s
        while cur not in seen:
            seen.add(cur)
            cyc.append(cur)
            cur = ((cur[0] + 2) % ncols, (cur[1] - 1) % w)
        cycles.append(cyc)
    return cycles


# --------------------------------------------------------------------------
# staged evaluation
# --------------------------------------------------------------------------

def closure_step(P, two, targets, done):
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
            if t not in two or True:
                pass
            for a in list(P):
                two.add(a ^ t)
            P.append(t)
            two.add(t)
            changed = True
    return changed


def evaluate(helpers_by_stage, natoms, targets):
    """helpers_by_stage: list of stages; each stage is a list of index triples
    into the availability list as of the start of that stage (plus helpers
    already emitted within the stage)."""
    P = [0] + [1 << i for i in range(natoms)]
    two = set()
    for a in P:
        for b in P:
            two.add(a ^ b)
    done = set()
    while closure_step(P, two, targets, done):
        pass
    for stage in helpers_by_stage:
        for tri in stage:
            n = len(P)
            v = P[tri[0] % n] ^ P[tri[1] % n] ^ P[tri[2] % n]
            for a in list(P):
                two.add(a ^ v)
            P.append(v)
            two.add(v)
        while closure_step(P, two, targets, done):
            pass
    return len(targets) - len(done)


def standard_construction(ncols, w, idx, rows=5):
    """2 helpers per node, all in one stage. Returns index triples."""
    natoms = ncols * rows * w
    # availability at stage start: [0] + atoms  -> index of atom i is i+1
    tri = []
    pos = 1 + natoms  # next helper lands here
    for x in range(ncols):
        for b in range(w):
            a = [idx[(x, y, b)] + 1 for y in range(rows)]
            tri.append((a[0], a[1], a[2]))
            t_at = pos
            pos += 1
            tri.append((t_at, a[3], a[4]))
            pos += 1
    return tri


def local_search(base_tri, drop, natoms, targets, nstage_split, iters=40000,
                 seed=0, T0=3.0, T1=0.15):
    """Delete helper #drop from the standard construction, then anneal all
    helper input choices (2 stages) to repair."""
    rng = random.Random(seed)
    tri = [list(t) for i, t in enumerate(base_tri) if i != drop]
    nh = len(tri)
    split = min(nstage_split, nh)

    def stages(tr):
        return [[tuple(t) for t in tr[:split]], [tuple(t) for t in tr[split:]]]

    cur = evaluate(stages(tri), natoms, targets)
    best, best_tri = cur, [list(t) for t in tri]
    if cur == 0:
        return 0, best_tri
    limit = 1 + natoms + nh + len(targets)
    for it in range(iters):
        Temp = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        gi = rng.randrange(nh)
        si = rng.randrange(3)
        cand = [list(t) for t in tri]
        cand[gi][si] = rng.randrange(limit)
        s = evaluate(stages(cand), natoms, targets)
        if s <= cur or rng.random() < math.exp((cur - s) / Temp):
            tri, cur = cand, s
            if cur < best:
                best, best_tri = cur, [list(t) for t in tri]
            if best == 0:
                return 0, best_tri
    return best, best_tri


def main():
    rows = 5
    for (ncols, w) in [(3, 1), (5, 1), (5, 2), (5, 4)]:
        natoms, idx, C, targets, tkey = make_problem(ncols, w, rows)
        cyc = node_cycle(ncols, w)
        std = standard_construction(ncols, w, idx, rows)
        base = evaluate([[tuple(t) for t in std], []], natoms, targets)
        print("=" * 70)
        print("analogue ncols=%d w=%d : %d atoms, %d targets, %d nodes, "
              "node-graph cycles=%s" % (ncols, w, natoms, len(targets),
                                        ncols * w, [len(c) for c in cyc]))
        print("  standard construction h=%d -> unresolved=%d %s"
              % (len(std), base, "(FEASIBLE)" if base == 0 else "(BROKEN)"))
        if base != 0:
            print("  !! standard construction not verified by the closure "
                  "model; skipping")
            continue
        budget = float(os.environ.get("REPAIR_BUDGET", 90))
        t_end = time.time() + budget
        bestall = None
        tried = 0
        drops = list(range(len(std)))
        random.Random(0).shuffle(drops)
        nh = len(std) - 1
        # splits control how many helpers may consume already-produced targets
        splits = sorted({nh, nh - 1, nh - 2, nh // 2, max(1, nh - 4)})
        rep = 0
        while time.time() < t_end:
            d = drops[tried % len(drops)]
            sp = splits[rep % len(splits)]
            tried += 1
            if tried % len(drops) == 0:
                rep += 1
            s, tr = local_search(std, d, natoms, targets, nstage_split=sp,
                                 iters=int(os.environ.get("REPAIR_ITERS", 3000)),
                                 seed=1234 + 97 * d + 7919 * rep)
            if bestall is None or s < bestall[0]:
                bestall = (s, d, tr)
            if s == 0:
                break
        print("  h=%d (one helper deleted): tried %d deletions, best "
              "unresolved=%d %s"
              % (len(std) - 1, tried, bestall[0],
                 "<-- REPAIRED, RECORD BEATEN" if bestall[0] == 0 else ""))
        if bestall[0] == 0:
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "repair_%d_%d.json" % (ncols, w)), "w") as f:
                json.dump({"ncols": ncols, "w": w,
                           "h": len(std) - 1,
                           "triples": bestall[2]}, f)
            print("  wrote repair_%d_%d.json" % (ncols, w))


if __name__ == "__main__":
    main()
