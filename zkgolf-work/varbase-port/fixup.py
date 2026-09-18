#!/usr/bin/env python3
"""Remove identifiers that a pruned build reports as unknown inside simp/rw lists.

Usage: fixup.py BUILD_LOG PACKAGE_DIR

For every `error: <file>:<line>:<col>: Unknown identifier `X`` whose position sits
inside a bracketed tactic argument list (`simp only [...]`, `rw [...]`,
`circuit_proof_start [...]`, ...), the identifier is deleted from the list.  These
are references that the elaborated proof never used (Lean's unused-simp-arg
linter flags the same spots), so removing them cannot change the proof term.
"""
import os, re, sys

LOG, PKG = sys.argv[1], sys.argv[2]
errs = []
for l in open(LOG, errors="replace"):
    m = re.match(r"error: Solution/Secp256k1ScalarMul/(\S+?)\.lean:(\d+):(\d+): (?:error\(lean\.unknownIdentifier\): )?Unknown identifier `([^`]+)`", l)
    if m:
        errs.append((m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)))
fixed = 0
for f, line, col, ident in errs:
    p = os.path.join(PKG, f + ".lean")
    src = open(p).read().split("\n")
    if line - 1 >= len(src):
        continue
    t = src[line - 1]
    # the identifier must sit inside a bracket list on this line (or a continuation line)
    before = t[:col]
    if "[" not in before and not re.match(r"^\s+[\w.'!?]+\s*[,\]]", t):
        continue
    pat = re.compile(r"(?<![\w.'])" + re.escape(ident) + r"(?![\w.'])")
    if not pat.search(t):
        continue
    # remove `ident,` or `, ident` or a lone `ident`
    t2 = re.sub(r"(?<![\w.'])" + re.escape(ident) + r"(?![\w.'])\s*,\s*", "", t, count=1)
    if t2 == t:
        t2 = re.sub(r",\s*(?<![\w.'])" + re.escape(ident) + r"(?![\w.'])", "", t, count=1)
    if t2 == t:
        t2 = pat.sub("", t, count=1)
    if t2 != t:
        src[line - 1] = t2
        open(p, "w").write("\n".join(src))
        fixed += 1
        print(f"fixed {f}:{line} removed {ident}")
print(f"{fixed} fixups applied out of {len(errs)} unknown-identifier errors")
