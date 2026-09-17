#!/usr/bin/env python3
"""Flatten the variable-base solution into a submission directory.

Collects the import closure of `Solution.Secp256k1ScalarMul.Main`, renames
`Solution/Secp256k1ScalarMul/Lazy/X.lean` to `Lazy_X.lean` (rewriting imports),
and refuses closures that still reach `Solution.Secp256k1ScalarMulFixedBase`.
"""
import os, re, sys, shutil

PROJ = sys.argv[1] if len(sys.argv) > 1 else "projs/secp256k1-scalar-mul"
OUT = sys.argv[2] if len(sys.argv) > 2 else "out/varbase-submission"
ROOT = "Solution.Secp256k1ScalarMul"

def path(mod):
    p = os.path.join(PROJ, *mod.split(".")) + ".lean"
    return p if os.path.exists(p) else None

def imports(mod):
    p = path(mod)
    if not p:
        return []
    return [m.group(1) for line in open(p)
            for m in [re.match(r"\s*import\s+(\S+)", line)] if m and m.group(1).startswith("Solution")]

seen, stack = set(), [ROOT + ".Main"]
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack += imports(m)
mods = sorted(m for m in seen if path(m))
bad = [m for m in mods if "FixedBase" in m]
if bad:
    print("ERROR: closure reaches fixed-base modules:", bad[:5])
    sys.exit(1)

def flat(mod):
    assert mod.startswith(ROOT + "."), mod
    return mod[len(ROOT) + 1:].replace(".", "_")

shutil.rmtree(OUT, ignore_errors=True)
os.makedirs(OUT)
for m in mods:
    src = open(path(m)).read()
    def rw(match):
        target = match.group(1)
        if target.startswith(ROOT + ".") and path(target):
            return "import " + ROOT + "." + flat(target)
        return match.group(0)
    src = re.sub(r"^import\s+(\S+)", rw, src, flags=re.M)
    open(os.path.join(OUT, flat(m) + ".lean"), "w").write(src)
print(len(mods), "files written to", OUT)
