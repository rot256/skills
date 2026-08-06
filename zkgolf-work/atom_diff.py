#!/usr/bin/env python3
"""Atom diff between two Lean solution trees.

Four steps, per the procedure recorded after the pointValidCount miss:
  1. collect atoms BY FILE (a name can live in a file you don't expect)
  2. report atoms MISSING from either side, never silently treat as equal
  3. reconcile the declared Main.lean totals
  4. flag regressions explicitly
"""
import re, sys, os

PAT = re.compile(r"def\s+(\w+)\s*:\s*Count\s*:=\s*⟨\s*(\d+)\s*,\s*(\d+)\s*⟩")

def atoms(root):
    out = {}
    for dp, _, fns in os.walk(root):
        for fn in fns:
            if not fn.endswith(".lean") and not fn.endswith(".lean.txt"):
                continue
            p = os.path.join(dp, fn)
            try:
                txt = open(p, errors="replace").read()
            except OSError:
                continue
            for m in PAT.finditer(txt):
                out[(fn, m.group(1))] = (int(m.group(2)), int(m.group(3)))
    return out

def total(root):
    for dp, _, fns in os.walk(root):
        if "Main.lean" in fns:
            txt = open(os.path.join(dp, "Main.lean"), errors="replace").read()
            a = re.search(r"allocations\s*:\s*Nat\s*:=\s*(\d+)", txt)
            c = re.search(r"constraints\s*:\s*Nat\s*:=\s*(\d+)", txt)
            if a and c:
                return int(a.group(1)), int(c.group(1))
    return None

old_root, new_root = sys.argv[1], sys.argv[2]
old_lbl = sys.argv[3] if len(sys.argv) > 3 else "old"
new_lbl = sys.argv[4] if len(sys.argv) > 4 else "new"

A, B = atoms(old_root), atoms(new_root)
to, tn = total(old_root), total(new_root)
print(f"{old_lbl}: {to} = {sum(to) if to else '?'}")
print(f"{new_lbl}: {tn} = {sum(tn) if tn else '?'}")

only_a = sorted(set(A) - set(B))
only_b = sorted(set(B) - set(A))
print(f"\nATOMS ONLY IN {old_lbl} ({len(only_a)}):")
for k in only_a:
    print(f"  {k[0]:38s} {k[1]:32s} {A[k]}")
print(f"\nATOMS ONLY IN {new_lbl} ({len(only_b)}):")
for k in only_b:
    print(f"  {k[0]:38s} {k[1]:32s} {B[k]}")

print("\nCHANGED ATOMS (shared name+file):")
regress = []
for k in sorted(set(A) & set(B)):
    if A[k] != B[k]:
        d = (B[k][0] - A[k][0]) + (B[k][1] - A[k][1])
        tag = "  <-- REGRESSION" if d > 0 else ""
        if d > 0:
            regress.append((k, A[k], B[k], d))
        print(f"  {k[0]:34s} {k[1]:30s} {A[k]} -> {B[k]}  {d:+d}{tag}")

print(f"\nREGRESSIONS vs {old_lbl}: {len(regress)}")
for k, a, b, d in regress:
    print(f"  {k[0]}::{k[1]}  {a} -> {b}  {d:+d}")
