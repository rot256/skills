#!/usr/bin/env python3
"""Declaration-level dead-code elimination for the flattened submission.

Inputs: a ranges file produced by `dce.lean` (lines `ALL <module> <s> <e>`,
`KEEP <module> <s> <e>`, `SUMMARY <module> ...`) and the flattened package
directory.  Every declaration range of a module that contains no constant in
the closure of the exported theorems is removed; modules that keep nothing are
deleted and their imports hoisted into their importers.
"""
import os, re, sys, shutil

RANGES, SRC, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
ROOT = "Solution.Secp256k1ScalarMul."
KEEP_EXTRA = set(sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()

def flat(mod):
    x = mod[len(ROOT):]
    return x.replace(".", "_") if not x.startswith("Lazy_Donor") else x

allr, keepr, mods = {}, {}, set()
for line in open(RANGES):
    p = line.split()
    if p[0] in ("ALL", "KEEP"):
        m = flat(p[1]); mods.add(m)
        (allr if p[0] == "ALL" else keepr).setdefault(m, set()).add((int(p[2]), int(p[3])))
    elif p[0] == "SUMMARY":
        mods.add(flat(p[1]))

files = {f[:-5] for f in os.listdir(SRC) if f.endswith(".lean")}
shutil.rmtree(OUT, ignore_errors=True)
os.makedirs(OUT)

deleted = set()
imports_of = {}
stats = []
for f in sorted(files):
    src = open(os.path.join(SRC, f + ".lean")).read().split("\n")
    imports_of[f] = [re.match(r"import " + re.escape(ROOT) + r"(\S+)", l).group(1)
                     for l in src if l.startswith("import " + ROOT)]
    keep = keepr.get(f, set()) | {r for r in allr.get(f, set()) if f + ":" + str(r[0]) in KEEP_EXTRA}
    if f in mods and not keep and f not in KEEP_EXTRA:
        deleted.add(f)
        continue
    n = len(src)
    mask = [True] * (n + 2)
    for (s, e) in allr.get(f, set()):
        if (s, e) in keep:
            continue
        for i in range(s, e + 1):
            mask[i] = False
    for (s, e) in keep:
        for i in range(s, e + 1):
            mask[i] = True
    # dangling `... in` prefixes and orphan doc comments above deleted blocks
    i = 1
    while i <= n:
        if not mask[i] and (i == 1 or mask[i - 1]):
            j = i - 1
            while j >= 1:
                t = src[j - 1].strip()
                if t == "":
                    j -= 1; continue
                if re.sub(r"--.*$", "", t).rstrip().endswith(" in") or t == "in":
                    mask[j] = False; j -= 1; continue
                if t.endswith("-/"):
                    # doc/comment block: delete back to its opening
                    k = j
                    while k >= 1 and not src[k - 1].lstrip().startswith("/-"):
                        k -= 1
                    if k >= 1 and src[k - 1].lstrip().startswith("/--"):
                        for q in range(k, j + 1):
                            mask[q] = False
                        j = k - 1; continue
                break
        i += 1
    out = [src[i - 1] for i in range(1, n + 1) if mask[i]]
    # collapse runs of blank lines
    res, blank = [], 0
    for l in out:
        if l.strip() == "":
            blank += 1
            if blank > 1: continue
        else:
            blank = 0
        res.append(l)
    stats.append((f, n, len(res)))
    open(os.path.join(OUT, f + ".lean"), "w").write("\n".join(res) + ("\n" if not res or res[-1] != "" else ""))

# import hoisting for deleted modules
def resolve(m, seen=None):
    seen = seen or set()
    out = []
    for i in imports_of.get(m, []):
        if i in deleted:
            if i not in seen:
                seen.add(i); out += resolve(i, seen)
        else:
            out.append(i)
    return out

for f in sorted(files - deleted):
    p = os.path.join(OUT, f + ".lean")
    src = open(p).read().split("\n")
    res, seen = [], set()
    for l in src:
        m = re.match(r"import " + re.escape(ROOT) + r"(\S+)$", l)
        if m:
            tgt = m.group(1)
            repl = resolve(tgt) if tgt in deleted else [tgt]
            for r in repl:
                if r not in seen:
                    seen.add(r); res.append("import " + ROOT + r)
        else:
            res.append(l)
    open(p, "w").write("\n".join(res))

tot_before = sum(n for _, n, _ in stats) + 0
tot_after = sum(k for _, _, k in stats)
print(f"deleted modules ({len(deleted)}): {' '.join(sorted(deleted))}")
print(f"kept modules: {len(stats)}; lines {tot_before} -> {tot_after}")
for f, n, k in sorted(stats, key=lambda x: -(x[1] - x[2]))[:25]:
    print(f"  {f:28s} {n:6d} -> {k:6d}")
