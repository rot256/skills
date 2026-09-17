#!/usr/bin/env python3
"""Merge groups of Lazy/*.lean modules into single files (submission file cap).

Each group is a list of module basenames in dependency order; the merged file
takes the first name.  Every member's body (imports stripped) is wrapped in a
`section … end` so file-level `open`/`set_option`/`attribute [local]` stay
scoped.  Imports of the merged file are the union of the members' imports minus
the members themselves; all other files importing a member are redirected.
"""
import os, re, sys

PROJ = sys.argv[1] if len(sys.argv) > 1 else "projs/secp256k1-scalar-mul"
LAZY = os.path.join(PROJ, "Solution", "Secp256k1ScalarMul", "Lazy")
MOD = "Solution.Secp256k1ScalarMul.Lazy."

GROUPS = [
    ["Interval", "Bounds", "Cert", "Cert3", "Relations", "MulCell"],
    ["CertsCost", "CertsShape", "CertsCW"],
    ["StepMath", "StepSpec", "StepValues"],
    ["StepCost", "StepOutput", "StepShape"],
    ["ProductsShape", "SquareCW", "NormalizeCW", "MuxVecCW", "ProductsCW"],
    ["LazyMSMFold", "LazyMSMSound", "LazyMSMFinal", "LazyMSMComplete"],
    ["LazyMSMCost", "LazyMSMShape", "LazyMSMCW"],
    ["PatternTableCost", "PatternTableCW"],
    ["PatBuildTable", "PatBuildTableCost"],
]

def read(name):
    return open(os.path.join(LAZY, name + ".lean")).read()

def split_imports(src):
    imps, body = [], []
    for line in src.splitlines():
        m = re.match(r"\s*import\s+(\S+)", line)
        if m:
            imps.append(m.group(1))
        else:
            body.append(line)
    return imps, "\n".join(body)

renamed = {}
for group in GROUPS:
    target = group[0]
    members = set(MOD + g for g in group)
    imports, bodies = [], []
    for g in group:
        imps, body = split_imports(read(g))
        for i in imps:
            i = renamed.get(i, i)
            if i not in members and i not in imports:
                imports.append(i)
        bodies.append(f"\n/-! ## merged from `Lazy/{g}.lean` -/\nsection\n{body.strip()}\nend\n")
    out = "\n".join("import " + i for i in imports) + "\n" + "".join(bodies)
    for g in group[1:]:
        os.remove(os.path.join(LAZY, g + ".lean"))
        renamed[MOD + g] = MOD + target
    open(os.path.join(LAZY, target + ".lean"), "w").write(out)
    print("merged", group, "->", target)

# redirect imports everywhere
for dirpath, _, files in os.walk(os.path.join(PROJ, "Solution")):
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dirpath, f)
        src = open(p).read()
        new = re.sub(r"^import\s+(\S+)", lambda m: "import " + renamed.get(m.group(1), m.group(1)), src, flags=re.M)
        # drop duplicate import lines
        seen, lines = set(), []
        for line in new.splitlines():
            if line.startswith("import "):
                if line in seen:
                    continue
                seen.add(line)
            lines.append(line)
        new = "\n".join(lines) + ("\n" if new.endswith("\n") else "")
        if new != src:
            open(p, "w").write(new)
print("done")
