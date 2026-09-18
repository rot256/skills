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

allr, keepr, mods, names = {}, {}, set(), {}
for line in open(RANGES):
    p = line.split()
    if p[0] in ("ALL", "KEEP"):
        m = flat(p[1]); mods.add(m)
        (allr if p[0] == "ALL" else keepr).setdefault(m, set()).add((int(p[2]), int(p[3])))
    elif p[0] == "NAMES":
        m = flat(p[1])
        names.setdefault(m, {})[(int(p[2]), int(p[3]))] = p[4:]
    elif p[0] == "SUMMARY":
        mods.add(flat(p[1]))

orig_keep = {m: set(v) for m, v in keepr.items()}
last_count = {}
for _f, _rs in names.items():
    for _r, _ns in _rs.items():
        for _n in _ns:
            _l = _n.split(".")[-1]
            last_count[_l] = last_count.get(_l, 0) + 1

def real_name(n):
    # strip private-name mangling `_private.<mod>.0.<name>`
    if n.startswith("_private."):
        i = n.find(".0.")
        if i >= 0: n = n[i + 3:]
    return n

# Textual keep rule: a declaration whose (last-component or `A.b`) name occurs as an
# identifier token in a kept line of the same module (or, qualified, anywhere) is kept
# even if no proof term mentions it (rfl lemmas used by dsimp, `rw [X.def]` unfolds).
TOK = re.compile(r"[A-Za-z_][\w'!?₀-₉.]*")
srcs = {f[:-5]: open(os.path.join(SRC, f)).read().split("\n") for f in os.listdir(SRC) if f.endswith(".lean")}
for _round in range(4):
    kept_tokens_mod, kept_tokens_all, kept_last_tokens_all = {}, set(), set()
    for f, src in srcs.items():
        keep = keepr.get(f, set())
        dele = set()
        for (s, e) in allr.get(f, set()):
            if (s, e) not in keep: dele.update(range(s, e + 1))
        toks = set()
        for i, l in enumerate(src, 1):
            if i in dele or l.startswith("import "): continue
            for t in TOK.findall(l):
                toks.add(t)
                if "." in t:
                    parts = t.split(".")
                    for j in range(len(parts)):
                        toks.add(".".join(parts[j:]))
        kept_tokens_mod[f] = toks
        kept_tokens_all |= {t for t in toks if "." in t}
        kept_last_tokens_all |= {t.split(".")[-1] for t in toks}
    added = 0
    for f in srcs:
        for r, ns in names.get(f, {}).items():
            if r in keepr.get(f, set()): continue
            size = r[1] - r[0] + 1
            if size > 6: continue   # only small helpers
            body = "\n".join(srcs[f][r[0] - 1:r[1]])
            rfl_body = re.search(r":=\s*(by\s+)?rfl\b|^\s*(@\[[^\]]*\]\s*)?(private\s+|protected\s+)?(abbrev|notation|macro)\b", body, re.M) is not None
            attributed = re.search(r"@\[[^\]]*(simp|circuit_norm|reducible)", body) is not None
            hit = False
            if rfl_body and attributed and size <= 4:
                hit = True   # rule C: simp-set rfl lemmas act invisibly through dsimp
            for n in ns:
                if hit: break
                n = real_name(n)
                parts = n.split(".")
                last = parts[-1]
                if last.startswith("_") or last in ("mk", "rec", "recOn", "casesOn", "noConfusion", "injEq", "sizeOf_spec"): continue
                if rfl_body and size <= 3 and (last in kept_tokens_mod.get(f, set()) or
                        (last in kept_last_tokens_all and last_count.get(last, 0) == 1)):
                    hit = True; break   # rule A: reference to a rfl helper (anywhere, if the name is unique)
                if len(parts) >= 2 and ".".join(parts[-2:]) in kept_tokens_all:
                    hit = True; break   # rule B: qualified reference anywhere
            if hit:
                keepr.setdefault(f, set()).add(r); added += 1
    print(f"textual keep round {_round}: +{added} declarations")
    if added == 0: break
# textual keeps must be closed under dependencies by the Lean side: emit them as seeds
extra_path = os.environ.get("DCE_EXTRA_OUT")
if extra_path:
    old = set(open(extra_path).read().split(",")) if os.path.exists(extra_path) else set()
    old.discard("")
    new = set()
    for f, rs in keepr.items():
        for (s0, e0) in rs:
            if (s0, e0) not in orig_keep.get(f, set()):
                mod = ROOT + (f if f.startswith("Lazy_Donor") or not f.startswith("Lazy_") else "Lazy." + f[5:])
                new.add(f"{mod}:{s0}")
    allx = old | new
    open(extra_path, "w").write(",".join(sorted(allx)))
    print(f"textual seeds: {len(new - old)} new, {len(allx)} total -> {extra_path}")

files = {f[:-5] for f in os.listdir(SRC) if f.endswith(".lean")}
shutil.rmtree(OUT, ignore_errors=True)
os.makedirs(OUT)

deleted = set()
imports_of = {}
stats = []
deleted_q2, kept_q2 = set(), set()
deleted_last_g, kept_last_g = set(), set()
deleted_ns, kept_ns = set(), set()
for f in files:
    for (s0, e0), ns in names.get(f, {}).items():
        kept_here = (s0, e0) in keepr.get(f, set())
        tgt = kept_q2 if kept_here else deleted_q2
        for nm in ns:
            parts = real_name(nm).split(".")
            if len(parts) >= 2: tgt.add(".".join(parts[-2:]))
            (kept_last_g if kept_here else deleted_last_g).add(parts[-1])
            if len(parts) >= 4:   # Solution.<Instance>.<Namespace>.<...>
                (kept_ns if kept_here else deleted_ns).add(parts[2])
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
    # notation-like commands (their auxiliary constants are never referenced by terms)
    for (s, e) in allr.get(f, set()):
        first = next((src[i - 1] for i in range(s, e + 1) if src[i - 1].strip()), "")
        if re.match(r"^\s*(@\[[^\]]*\]\s*)?((local|scoped)\s+)?(notation|macro|syntax|macro_rules|elab|elab_rules|infix|infixl|infixr|prefix|postfix|binder_predicate|declare_syntax_cat)\b", first):
            for i in range(s, e + 1):
                mask[i] = True
    # a deleted declaration's range may stop at its header line (structure fields,
    # `where` bodies): also delete the indented continuation lines and a trailing `deriving`
    i = 1
    while i <= n:
        if not mask[i] and (i == n or mask[i + 1]):
            j = i + 1
            while j <= n and (src[j - 1].strip() == "" or src[j - 1][0] in " \t" or src[j - 1].startswith("deriving ")):
                if src[j - 1].strip() != "":
                    mask[j] = False
                j += 1
            i = j; continue
        i += 1
    # stray commands that may mention deleted names: `#print`/`#eval`/`#check`/`#guard`
    # lines, and `example` blocks (an example extends over the following indented lines)
    i = 1
    while i <= n:
        t = src[i - 1]
        if re.match(r"#(print|eval|check|guard|reduce|synth)\b", t):
            mask[i] = False
        elif re.match(r"(private |protected |noncomputable )*example\b", t):
            mask[i] = False
            j = i + 1
            while j <= n and (src[j - 1].strip() == "" or src[j - 1][0] in " \t"):
                mask[j] = False; j += 1
            i = j; continue
        i += 1
    # plain `open A B C` naming namespaces that no longer hold any declaration
    for i in range(1, n + 1):
        if not mask[i]: continue
        m = re.match(r"^(\s*open\s+)([\w.]+(?:\s+[\w.]+)*)\s*$", src[i - 1])
        if m and "(" not in src[i - 1]:
            toks = m.group(2).split()
            keep_toks = [t for t in toks if not (t.split(".")[-1] in deleted_ns and t.split(".")[-1] not in kept_ns)]
            if not keep_toks:
                mask[i] = False
            elif len(keep_toks) != len(toks):
                src[i - 1] = m.group(1) + " ".join(keep_toks)
    # `open X (a b ...)` selective opens (possibly spanning lines) may name deleted
    # declarations: drop those names (keeping the list selective, since widening
    # changes name resolution inside proofs)
    i = 1
    while i <= n:
        m = re.match(r"^(\s*open\s+[\w.]+(?:\s+[\w.]+)*)\s*\(", src[i - 1])
        if m and mask[i]:
            j = i
            while j <= n and ")" not in src[j - 1]:
                j += 1
            text = "\n".join(src[i - 1:j])
            inner = text[text.index("(") + 1:text.rindex(")")]
            ns_last = m.group(1).split()[-1].split(".")[-1]
            ids = [x for x in inner.split()
                   if not (ns_last + "." + x in deleted_q2 and ns_last + "." + x not in kept_q2)]
            if ids:
                src[i - 1] = m.group(1) + " (" + " ".join(ids) + ")"
            else:
                mask[i] = False
            for q in range(i + 1, j + 1):
                mask[q] = False
            i = j + 1; continue
        i += 1
    # `attribute [...] a b c` lines naming deleted declarations of this module
    deleted_last = set()
    for (s0, e0), ns in names.get(f, {}).items():
        if (s0, e0) in keep: continue
        for nm in ns:
            deleted_last.add(real_name(nm).split(".")[-1])
    for i in range(1, n + 1):
        if not mask[i]: continue
        m = re.match(r"^(\s*attribute\s*\[[^\]]*\]\s*)(.*?)(\s+in)?\s*$", src[i - 1])
        if m:
            ids = m.group(2).split()
            kept_ids = [x for x in ids if not (x.split(".")[-1] in deleted_last or
                        (x.split(".")[-1] in deleted_last_g and x.split(".")[-1] not in kept_last_g))]
            if not kept_ids:
                mask[i] = False
            elif len(kept_ids) != len(ids):
                src[i - 1] = m.group(1) + " ".join(kept_ids) + (m.group(3) or "")
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
