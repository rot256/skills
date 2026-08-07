#!/usr/bin/env python3
"""zkGolf/Aristotle loop tick. Runtime state is regenerable from the zk.golf + Aristotle
APIs (see bootstrap.sh); only this tooling needs to persist. Location-independent."""
import os, sys, re, json, glob, time, tarfile, asyncio, datetime, subprocess, shutil
import requests, aristotlelib
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
ZK = os.environ["ZKGOLF_KEY"]; H = {"Authorization": f"Bearer {ZK}"}
NOW = datetime.datetime.utcnow().isoformat() + "Z"
KEYS = {"primary": os.environ.get("ARISTOTLE_API_KEY", ""), "alt": os.environ.get("ARISTOTLE_API_KEY_ALT", "")}
def use_key(name): os.environ["ARISTOTLE_API_KEY"] = KEYS.get(name) or KEYS["primary"]
SLUG2INST = {"gf2-k12-compress-canonical":"KangarooTwelveGF2","gf2-sha256-compress-canonical":"SHA256CompressGF2Canonical","sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
CHALLENGES5 = list(SLUG2INST)
# Slugs we no longer DISPATCH to, while still keeping them in SLUG2INST so in-flight jobs are
# still adopted, processed and submitted normally.
#
# gf2-k12: a submission that merely TIES the baseline does not make the leaderboard, so our
# verified 38400 (= 2 x 19200, one AND per state bit) scores nothing and only <= 19199 ANDs
# would. That is provably out of reach here: over ZMod 2 every output is affine in (x, w), so
# quotienting by affine functions gives T >= dim span of the outputs' classes, and one Keccak
# round has 1600 linearly independent degree-2 monomials u_{i+1}u_{i+2} => EXACTLY 1600 rows
# per round, 19200 for twelve. The bound is a dimension count, hence additive across the 320
# parallel chi instances, so the "joint MC" hope is dead; it also survives full nondeterminism
# and re-proves MC(chi_5) >= 5 without a SAT solver. Cross-round reuse is separately impossible
# (rank(rhoPi o theta) = 1600, so round r products have degree 2^r). Beating 19200 would be a
# publishable cryptography result, not a golf. Freeing these 4 slots for winnable challenges.
# Challenges with no remaining headroom worth a job slot. gf2-k12: a valid submission only TIES
# the 38400 baseline and a tie does not leaderboard. rsa: we hold 321889 and the measured floor is
# ~321671 (0.068%), its one named lever re-measured from 1467 down to 218, and "assertion, not value"
# is provably inapplicable because every materialised value there is an OPERAND, not a target.
NO_DISPATCH = {"gf2-k12-compress-canonical", "rsa-pkcs1v15-sha256-4096-65537"}
DISPATCH = [s for s in CHALLENGES5 if s not in NO_DISPATCH]
def load(p, d):
    try: return json.load(open(p))
    except Exception: return d
def save(p, o):
    # Atomic: a container death mid-write once truncated state_jobs.json, and `load` turns an
    # unparseable file into {} — which reads as "no jobs" and re-dispatches the whole fleet.
    # Write to a temp file, fsync, then rename: readers see either the old file or the new one.
    tmp = p + ".tmp"
    with open(tmp, "w") as f:
        json.dump(o, f, indent=2); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, p)
def audit(p, rec):
    with open(p, "a") as f: f.write(json.dumps(rec) + "\n")
def leaderboard_best(slug):
    try:
        for c in requests.get("https://zk.golf/api/agent/v1/challenges", headers=H, timeout=30).json():
            if c["slug"] == slug: return c["best_score"]
    except Exception: pass
    return None
def strip_comments(t):
    return re.sub(r"--[^\n]*", " ", re.sub(r"/-.*?-/", " ", t, flags=re.S))
def has_holes(soldir):
    for f in glob.glob(os.path.join(soldir, "*.lean")):
        if "/.lake/" in f: continue
        t = strip_comments(open(f, errors="ignore").read())
        for bad in ("sorry", "admit", "native_decide"):
            if re.search(r"\b" + bad + r"\b", t): return bad
    return None
def missing_required(soldir):
    req = ["soundness","completeness","mainCost","isR1CS","computableWitness"]; blob = ""
    for f in glob.glob(os.path.join(soldir, "*.lean")):
        if "/.lake/" in f: continue
        blob += open(f, errors="ignore").read()
    return [r for r in req if (f"theorem {r}" not in blob and f"{r} :" not in blob)]
def parse_cost(soldir):
    # Read the EXPORTED cost only. This used to glob every .lean and take the first hit, which meant an
    # `allocations` in some auxiliary or candidate cost file could be reported as the circuit's score.
    # Measured: eleven sha256 jobs all "found" 72207/72789 because a leftover CostSparseMain.lean was
    # being read instead of their own tree, whose honest score equalled the record. The submission guard
    # `score >= best` therefore never fired. Main.lean is the single source of truth; follow one level of
    # re-export (Main.lean is often just `import Solution.X.MainSparse`) but never fall back to a glob.
    def grab(t):
        ma = re.search(r"def\s+allocations\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t)
        mc = re.search(r"def\s+constraints\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t)
        return (int(ma.group(1)) if ma else None), (int(mc.group(1)) if mc else None)
    main = os.path.join(soldir, "Main.lean")
    if not os.path.exists(main): return None, None
    txt = open(main, errors="ignore").read()
    a, c = grab(txt)
    if a is None or c is None:
        for imp in re.findall(r"^import\s+[A-Za-z0-9_.]*\.([A-Za-z0-9_]+)\s*$", txt, re.M):
            f = os.path.join(soldir, imp + ".lean")
            if not os.path.exists(f): continue
            a2, c2 = grab(open(f, errors="ignore").read())
            a = a if a is not None else a2
            c = c if c is not None else c2
            if a is not None and c is not None: break
    return a, c
XPOLL_MARK = {  # if the seed's cross-pollinated gadget appears, credit the technique
    "rsa-pkcs1v15-sha256-4096-65537": ("EqViaCarriesFlex", "flexible-limb equality/carry (ported from secp)"),
    "secp256k1-scalar-mul": ("EqViaCarriesFlex", "flexible-limb equality/carry (ported from secp-fixed)"),
    "secp256k1-fixed-base-scalar-mul": ("GroupedEqXV", "XV equality-grouping (ported from secp-mul)"),
}

# Technique fingerprints: (marker, label). A marker matches if it appears in a Solution
# FILENAME or anywhere in the Solution source. Order is the order they get listed, so put
# the structurally important ones first. Labels are terse on purpose — the description
# field is a one-liner on a public leaderboard, not a paper.
TECHNIQUES = {
    "secp256k1-scalar-mul": [
        ("GLVScalarMul", "4-dim fake-GLV: result witnessed, closed by an =O assertion"),
        ("FoldTarget", "pseudo-Mersenne quotient fold (1-wire quotient, 71-bit check)"),
        ("InterpMul", "limb products at 2m-1 evaluation points (7 rows, not 16)"),
        ("FusedStep", "ELM fused 2R+T, intermediate y never materialised"),
        ("GLVStepLastSlope", "slope-only terminal assertion (x_S = x_A)"),
        ("GroupedEq", "grouped carry propagation"),
        ("ValidPBytes", "canonicality bits reused as the output byte encoding"),
        ("DivOrZeroF3", "square muxed at polynomial level, one shared reduction"),
    ],
    "secp256k1-fixed-base-scalar-mul": [
        ("Comb", "width-12 all-odd signed-digit comb, 21+1 windows"),
        ("Recode", "recode is a wire permutation (0 rows); parity folded into the top table"),
        ("Select12", "factored one-hot (2^7 x 2^4), contracted per output wire"),
        ("ChainFold", "pseudo-Mersenne quotient fold"),
        ("ChainState", "accumulator carried as (x, lambda); y materialised once"),
        ("InterpMul", "limb products at 2m-1 evaluation points"),
        ("SparseCanonical", "sparse-prime canonicality"),
        ("EitherZero", "exceptional scalars screened by affine mismatch counts"),
    ],
    "sha256-hash": [
        ("PackedCh", "lambda-packed twin gadgets: Ch/Maj at 1/2 row per bit"),
        ("PackedMaj", "two-root row with an out-of-range decoy"),
        ("Xor3", "single-row XOR3 (booleanity absorbed)"),
        ("FusedAdders", "lambda-fused multi-operand mod-2^32 adds, no tie rows"),
        ("CarrySumAdd32", "affine carry chain: zero carry allocations"),
        ("ScheduleStepLast", "terminal schedule words left unreduced"),
        ("CheckLenFlags", "binomial-moment one-hot for the length flag"),
        ("Padding7", "7-of-8 bits per byte, high-bit checks paired"),
    ],
    "keccak-f1600": [
        ("Xor3Lane", "single-row 3-input XOR per bit"),
        ("ChiLane", "chi at one row per state bit (outer XOR folded in)"),
        ("Xor5Lane", "column parity as two chained single-row XOR3s"),
    ],
    "rsa-pkcs1v15-sha256-4096-65537": [
        ("ModExp", "e = 65537 as 16 squarings + 1 multiply (optimal addition chain)"),
        ("InterpMul", "limb products at 2m-1 evaluation points, interpolation free"),
        ("MulModLazy", "lazy reduction: products accumulate unreduced, one reduction shared"),
        ("SquareModLazy", "squaring symmetry: tri(m) coefficients, not m^2"),
        ("GroupedEqXV", "grouped carries with per-group widths"),
        ("BalancedZ", "balanced (signed) limb representation"),
        ("MixedRadix", "mixed-radix limb widths"),
        ("NormalizeTight", "tight normalisation bounds; top bit affine"),
        ("Repack24To16", "re-packing between limb widths across the exponentiation"),
        ("PadDigest", "PKCS#1 v1.5 padding checked against compile-time constants"),
    ],
}
for _s in ("gf2-sha256-compress-canonical", "gf2-k12-compress-canonical"):
    TECHNIQUES[_s] = [("", "GF(2): score = 2 x AND count, so this is a multiplicative-complexity result")]
DESC_MAX = 480  # keep the public one-liner readable
def techniques(slug, soldir):
    files = [f for f in glob.glob(os.path.join(soldir, "*.lean")) if "/.lake/" not in f]
    names = " ".join(os.path.basename(f) for f in files)
    body = None; out = []
    for marker, label in TECHNIQUES.get(slug, []):
        if not marker:
            out.append(label); continue
        if marker in names:
            out.append(label); continue
        if body is None:  # only read the sources if a filename match failed
            body = " ".join(open(f, errors="ignore").read() for f in files)
        if marker in body:
            out.append(label)
    return out
def describe(slug, score, alloc, constr, best, purpose, soldir):
    parts = [f"{score} = {alloc} alloc + {constr} constr"]
    if best is not None:
        b = int(best); d = int(score) - b
        parts.append(f"({d:+d} vs prev best {b})" if d else f"(matches best {b})")
    head = " ".join(parts)
    tech = techniques(slug, soldir)
    tag, note = XPOLL_MARK.get(slug, (None, None))
    if tag and any(tag in os.path.basename(f) for f in glob.glob(os.path.join(soldir, "*.lean"))):
        tech.append(note)
    tail = f"Aristotle {purpose or 'run'}"
    while tech and len(f"{head}. {'; '.join(tech)}. {tail}") > DESC_MAX:
        tech.pop()  # drop the least structurally important first
    return f"{head}. {'; '.join(tech)}. {tail}" if tech else f"{head} — {tail}"
def zk_submit(slug, alloc, constr, desc, files):
    fs = [("artifact", (os.path.basename(f), open(f, "rb"), "text/plain")) for f in files]
    data = {"allocations": str(alloc), "constraints": str(constr), "description": desc, "assisted_by": "Aristotle (Harmonic)"}
    r = requests.post(f"https://zk.golf/api/agent/v1/challenges/{slug}/submissions", headers=H, data=data, files=fs, timeout=120)
    return r.status_code, r.text
SALVAGE_ATTEMPTS = 6  # give up only after this many CONSECUTIVE non-improving proof-completion tries
def count_holes(soldir):
    n = 0
    for f in glob.glob(os.path.join(soldir, "*.lean")):
        if "/.lake/" in f: continue
        n += len(re.findall(r"\b(sorry|admit)\b", strip_comments(open(f, errors="ignore").read())))
    return n
def stage_salvage(slug, soldir, score):
    # A near-miss: circuit BEATS the record but has only `sorry`/`admit`. Stash the full project
    # with this Solution swapped in so a follow-up job completes just the proof. KEEP PUSHING on
    # partial progress: re-stage (resetting the attempt counter) whenever a result improves either
    # cost OR the number of remaining holes, so we build on half-finished work instead of restarting.
    sal = load("state_salvage.json", {}); holes = count_holes(soldir); cur = sal.get(slug)
    if cur:
        ch = cur.get("holes", 1 << 30)
        # progress = closer to a complete proof (fewer holes), ties broken by lower cost. Any
        # below-record valid solution is a win, so proof-completion outranks marginal cost.
        improved = (holes < ch) or (holes == ch and score < cur["score"])
        if not improved and cur.get("attempts", 0) < SALVAGE_ATTEMPTS:
            return False  # no progress and not yet exhausted → keep working the current snapshot
    inst = SLUG2INST[slug]; dst = os.path.join("salvage", slug)
    shutil.rmtree(dst, ignore_errors=True)
    shutil.copytree(f"projs/{slug}", dst)  # full project (Challenge/, lakefile, configs, reference/)
    soldst = os.path.join(dst, "Solution", inst)
    for f in glob.glob(soldst + "/*.lean"): os.remove(f)
    for f in glob.glob(soldir + "/*.lean"): shutil.copy(f, soldst)
    sal[slug] = {"score": score, "holes": holes, "attempts": 0}; save("state_salvage.json", sal)
    return True
def salvage_prompt(slug, score):
    inst = SLUG2INST[slug]
    return (f"You are FINISHING half-completed work in the Clean Lean-4 framework (clean @ 041c6e7e, Lean v4.28.0) — "
            f"do NOT start over.\n\n"
            f"`Solution/{inst}/` ALREADY contains a circuit at cost (allocations+constraints) {score}, BELOW the current "
            f"record. MOST proofs are already DONE; only a few `sorry`/`admit` placeholders remain. Your ONLY job is to "
            f"CONTINUE this exact solution and close those remaining holes so the whole thing verifies — reuse every "
            f"lemma and structure that is already there; do not rewrite what already works. Do NOT change the circuit "
            f"shape, `main`, `allocations`, or `constraints` unless strictly required to close a proof, and then keep "
            f"cost <= {score}. Even partial progress helps: if you cannot close every hole, close as many as you can and "
            f"return the result with the rest still marked — a solution with FEWER remaining `sorry`s is real progress we "
            f"will build on next. If you DO close them all: keep ALL required declarations (`soundness`,`completeness`,"
            f"`mainCost`,`isR1CS`,`computableWitness`), no `native_decide`, permitted axioms only, and MANDATORY run "
            f"`lake build` to ZERO errors + `#print axioms` (no `sorryAx`) before returning the complete Solution/{inst}/.")
async def process_jobs():
    st = load("state_jobs.json", {})
    for pid, j in list(st.items()):
        if j.get("processed"): continue
        slug = j["slug"]; inst = SLUG2INST[slug]; use_key(j.get("key", "primary"))
        try:
            p = await aristotlelib.Project.from_id(pid); await p.refresh()
        except Exception as e:
            print(f"STATUS: {slug} {pid[:8]} refresh-error {e}"); continue
        status = getattr(p.status, "name", str(p.status)); j["status"] = status
        if status == "IDLE":
            outdir = os.path.join("out", slug); tarp = os.path.join(outdir, "solution.tar.gz")
            try:
                if not getattr(p, "has_files", True):
                    print(f"NOTIFY: aristotle {slug} produced no files"); j["processed"]=True; st[pid]=j; continue
                # WIPE FIRST. This directory used to be reused across jobs, so extractall() UNIONED every
                # job's tree with every previous job's leftovers, and the submission shipped the union.
                # Measured on sha256-hash: 203 files in the job's own tarball, 246 on disk, 43 stale — and
                # 119 duplicate fully-qualified declarations, which is a hard Lean build error. That is why
                # nineteen consecutive sha256 submissions failed. The leftover count tracked the failure
                # rate exactly across slugs: fixed-base 1 leftover (verifies), scalar-mul 6 (verifies),
                # sha256 43 (never verified). Preserved submitted-*.tar.gz files are kept deliberately.
                keep = {os.path.basename(f) for f in glob.glob(os.path.join(outdir, "submitted-*.tar.gz"))}
                if os.path.isdir(outdir):
                    for e in os.listdir(outdir):
                        if e in keep: continue
                        pth = os.path.join(outdir, e)
                        shutil.rmtree(pth) if os.path.isdir(pth) else os.remove(pth)
                os.makedirs(outdir, exist_ok=True)
                await p.get_files(destination=tarp)
                with tarfile.open(tarp) as tf: tf.extractall(outdir)
            except Exception as e:
                print(f"STATUS: {slug} download-error {e}"); continue
            soldirs = [d for d in glob.glob(os.path.join(outdir, "**", "Solution", inst), recursive=True) if "/.lake/" not in d]
            if not soldirs:
                print(f"NOTIFY: aristotle {slug} no Solution/{inst}"); j["processed"]=True; st[pid]=j; continue
            soldir = soldirs[0]; hole = has_holes(soldir); alloc, constr = parse_cost(soldir)
            best = leaderboard_best(slug); score = (alloc + constr) if (alloc is not None and constr is not None) else None
            j.update({"alloc": alloc, "constr": constr, "score": score, "best": best})
            if hole:
                # near-miss salvage: sorry/admit-only hole on a circuit that BEATS the record → stash for proof-completion
                if hole in ("sorry","admit") and score is not None and best is not None and score < best and not missing_required(soldir):
                    if stage_salvage(slug, soldir, score):
                        print(f"NOTIFY: aristotle {slug} near-miss {score} (< {best}) has `{hole}` — STAGED for proof-completion salvage")
                    else:
                        print(f"NOTIFY: aristotle {slug} near-miss {score} `{hole}` — salvage already pending; skipped")
                else:
                    print(f"NOTIFY: aristotle {slug} contains `{hole}` (score~{score} vs {best}); NOT submitting")
                j["processed"]=True; st[pid]=j; continue
            miss = missing_required(soldir)
            if miss: print(f"NOTIFY: aristotle {slug} MISSING {miss} — NOT submitting"); j["processed"]=True; st[pid]=j; continue
            if score is None: print(f"NOTIFY: aristotle {slug} unparseable cost"); j["processed"]=True; st[pid]=j; continue
            if best is not None and score >= best: print(f"NOTIFY: aristotle {slug} score {score} does NOT beat best {best} — NOT submitting"); j["processed"]=True; st[pid]=j; continue
            files = sorted(glob.glob(os.path.join(soldir, "*.lean")))
            if len(files) > 1000:  # zkGolf accepts at most 1000 files; larger submissions 400
                print(f"NOTIFY: aristotle {slug} score {score} BEATS best {best} but has {len(files)}>1000 files — cannot submit, needs consolidation")
                j["processed"] = True; st[pid] = j; continue
            desc = describe(slug, score, alloc, constr, best, j.get("purpose"), soldir)
            code, text = zk_submit(slug, alloc, constr, desc, files)
            try: sid = json.loads(text).get("id")
            except Exception: sid = None
            print(f"NOTIFY: SUBMITTED {slug} score {score} (best {best}) http={code} sub={sid}")
            if sid:
                subs = load("state_subs.json", {}); subs[sid] = {"slug": slug, "score": score, "status": "pending", "ts": NOW}
                save("state_subs.json", subs); audit("submissions.jsonl", subs[sid] | {"submission_id": sid}); j["zk_id"] = sid
                # Preserve the exact tree we submitted. out/<slug>/solution.tar.gz is overwritten by the
                # NEXT job for this slug, so a verifier timeout — which is infrastructure, not a bad
                # solution — otherwise loses a valid improvement permanently. Measured: fixed-base 50379
                # timed out and its tree was already gone by the time we went looking. Pruned below once
                # the submission reaches a terminal state that is not a timeout, so disk stays bounded.
                try: shutil.copyfile(tarp, os.path.join(outdir, f"submitted-{sid}.tar.gz"))
                except Exception as e: print(f"STATUS: {slug} could not preserve submitted tree: {e}")
                sal = load("state_salvage.json", {})  # a beating submission landed → stop salvaging this slug
                if slug in sal and score <= sal[slug].get("score", 1 << 62): del sal[slug]; save("state_salvage.json", sal)
            j["processed"] = True
        else:
            print(f"STATUS: aristotle {slug} {status}")  # never auto-cancel long-running jobs
        st[pid] = j
    save("state_jobs.json", st)
def regen_prompts_if_stale():
    """Prompts are gitignored, so a filesystem/container rollback can revert them while
    research.json stays current — silently dispatching stale prompts. Regenerate whenever
    any prompt is older than research.json/gen_prompts.py, or is missing/empty."""
    try:
        srcs = [os.path.join(HERE, f) for f in ("research.json", "gen_prompts.py")]
        newest = max(os.path.getmtime(f) for f in srcs if os.path.exists(f))
        outs = [os.path.join(HERE, d, f"{sl}.md") for d in ("prompts", "prompts_small") for sl in CHALLENGES5]
        outs = [f for f in outs if os.path.exists(f)] or None
        if outs is None:
            subprocess.run([sys.executable, os.path.join(HERE, "gen_prompts.py")], check=True, capture_output=True, timeout=120)
            print("STATUS: prompts missing — generated from research.json"); return
        stale = any(os.path.getsize(f) == 0 for f in outs) or min(os.path.getmtime(f) for f in outs) < newest
        if stale:
            subprocess.run([sys.executable, os.path.join(HERE, "gen_prompts.py")], check=True, capture_output=True, timeout=120)
            print("STATUS: prompts were stale — regenerated from research.json")
    except Exception as e:
        print(f"STATUS: prompt regen check failed {e}")


KEYS_TO_USE = ["primary"] + (["alt"] if KEYS.get("alt") else [])  # dual-account fleet
async def reconcile_orphans(st):
    """A filesystem rollback wipes state_jobs.json but NOT the Aristotle side, so its jobs keep
    running as orphans: we never poll them (their results are lost) and they still count against
    the per-key RUNNING cap, starving refill. Re-adopt every RUNNING project whose description
    names a known challenge so its result is harvested and the state reflects reality."""
    for kname in KEYS_TO_USE:
        use_key(kname)
        try:
            ps, pk = [], None
            while True:
                page, pk = await aristotlelib.Project.list_projects(
                    pagination_key=pk, limit=30, status=aristotlelib.ProjectStatus.RUNNING)
                ps += page
                if not pk: break
        except Exception as e:
            print(f"STATUS: reconcile {kname} list failed {e}"); continue
        for p in ps:
            pid = str(p.project_id)
            if pid in st: continue
            slug = (getattr(p, "description", "") or "").strip()
            if slug not in SLUG2INST:
                print(f"STATUS: reconcile {kname} {pid[:8]} description {slug!r} not a challenge — leaving alone"); continue
            # keep slot bookkeeping honest: take a free (slug,purpose,key) slot, else mark "extra"
            taken = set((j["slug"], j.get("purpose"), j.get("key", "primary")) for j in st.values() if not j.get("processed"))
            purpose = next((pp for pp in ("big-win", "small-win") if (slug, pp, kname) not in taken), "extra")
            st[pid] = {"slug": slug, "status": "RUNNING", "processed": False, "purpose": purpose,
                       "key": kname, "ts": NOW, "salvage": False, "adopted": True}
            print(f"NOTIFY: adopted orphaned job {slug} [{purpose}/{kname}] {pid[:8]} — state had lost it")
PRIMARY_STALL_HOURS = float(os.environ.get("PRIMARY_STALL_HOURS", "2"))
PRIMARY_PROBE_CAP   = int(os.environ.get("PRIMARY_PROBE_CAP", "1"))

async def primary_dispatch_cap(st):
    """Rate-limit the primary account while it ACCEPTS jobs but does not RUN them.

    Observed 2026-08-04: all 12 primary projects sat with their agent task QUEUED and zero
    progress events for ~13h while the alt account executed normally — half the fleet was dead
    weight, and nothing in our state showed it, because `Project.status == RUNNING` only means
    the project EXISTS. Task status is the real signal. Filling primary's slots in that state
    buries real work in a queue that is not draining, so cap it at a single probe job until one
    is seen running. Self-healing: the moment any primary task leaves QUEUED the cap lifts.
    """
    inflight = [(pid, j) for pid, j in st.items()
                if not j.get("processed") and j.get("key", "primary") == "primary"]
    if not inflight: return 10**6
    use_key("primary")
    oldest = 0.0; healthy = False; seen = 0
    for pid, j in inflight:
        try:
            p = await aristotlelib.Project.from_id(pid); await p.refresh()
            if getattr(p.status, "name", str(p.status)) == "IDLE":
                healthy = True; break                 # it finished something: definitely consuming
            tasks, _ = await p.get_tasks(limit=3)
            if not tasks: continue                    # taskless zombie: says nothing about health
            seen += 1
            if any(t.status.name != "QUEUED" for t in tasks): healthy = True; break
            age = (datetime.datetime.now(datetime.timezone.utc) -
                   datetime.datetime.fromisoformat(j["ts"].replace("Z", "+00:00"))).total_seconds() / 3600
            oldest = max(oldest, age)
        except Exception as e:
            print(f"STATUS: primary health probe {pid[:8]} {e}")
    if healthy or seen == 0 or oldest < PRIMARY_STALL_HOURS: return 10**6
    print(f"NOTIFY: primary key STALLED — {seen} jobs queued, oldest {oldest:.1f}h, none running; "
          f"capping primary dispatch at {PRIMARY_PROBE_CAP} until it drains")
    return PRIMARY_PROBE_CAP

async def ensure_inflight(st):
    # keep >=1 job per (challenge, big/small, account) in flight — up to 20 with two keys
    active = set((j["slug"], j.get("purpose"), j.get("key", "primary")) for j in st.values() if not j.get("processed"))
    sal = load("state_salvage.json", {})
    for slug in list(sal):  # retire exhausted near-misses...
        if sal[slug].get("attempts", 0) >= SALVAGE_ATTEMPTS:
            print(f"NOTIFY: salvage {slug} @{sal[slug]['score']} exhausted {SALVAGE_ATTEMPTS} tries — giving up"); del sal[slug]; continue
        # ...and any a competitor has since overtaken (completing it would no longer be a record)
        lb = leaderboard_best(slug)
        if lb is not None and sal[slug]["score"] >= lb:
            print(f"NOTIFY: salvage {slug} @{sal[slug]['score']} no longer beats record {int(lb)} — dropping"); del sal[slug]
    save("state_salvage.json", sal)
    regen_prompts_if_stale()
    pcap = await primary_dispatch_cap(st)
    pcount = sum(1 for j in st.values()
                 if not j.get("processed") and j.get("key", "primary") == "primary")
    for slug in DISPATCH:
        for purpose, pdir in (("big-win","prompts"), ("small-win","prompts_small")):
            for kname in KEYS_TO_USE:
                if (slug, purpose, kname) in active: continue
                if kname == "primary" and pcount >= pcap: continue
                # big-win slot preferentially completes a pending near-miss's proof
                do_salvage = purpose == "big-win" and slug in sal and sal[slug].get("attempts", 0) < SALVAGE_ATTEMPTS
                try:
                    use_key(kname)
                    if do_salvage:
                        proj_dir = f"salvage/{slug}"; prompt = salvage_prompt(slug, sal[slug]["score"])
                    else:
                        proj_dir = f"projs/{slug}"; prompt = open(f"{pdir}/{slug}.md").read()
                        if not prompt.strip():  # never submit an empty prompt
                            print(f"STATUS: {slug}/{purpose}/{kname} prompt EMPTY — skipping (run gen_prompts.py)")
                            continue
                    p = await aristotlelib.Project.create_from_directory(prompt=prompt, project_dir=proj_dir)
                    st[p.project_id] = {"slug": slug, "status": "SUBMITTED", "processed": False, "purpose": purpose, "key": kname, "ts": NOW, "salvage": do_salvage}
                    if do_salvage:
                        sal[slug]["attempts"] += 1; save("state_salvage.json", sal)
                        print(f"NOTIFY: auto-dispatched {slug} [SALVAGE proof-completion @{sal[slug]['score']}, attempt {sal[slug]['attempts']}/{SALVAGE_ATTEMPTS}] -> {p.project_id}")
                    else:
                        print(f"NOTIFY: auto-dispatched {slug} [{purpose}/{kname}] -> {p.project_id}")
                    if kname == "primary": pcount += 1
                except Exception as e:
                    print(f"STATUS: refill {slug}/{purpose}/{kname} failed {e}")
def process_subs():
    subs = load("state_subs.json", {})
    for sid, s in list(subs.items()):
        if s.get("status") in ("verified", "failed"): continue
        try:
            r = requests.get(f"https://zk.golf/api/agent/v1/submissions/{sid}", headers=H, timeout=30).json()
        except Exception as e:
            print(f"STATUS: sub {sid[:8]} poll-error {e}"); continue
        stt = r.get("status"); score = r.get("score")
        if stt == "timeout" and score is None:
            # the zk.golf verifier gave up, not the solution — a real improvement was dropped for
            # infrastructure reasons. Mark it terminal so we stop polling, but say so loudly.
            s["status"] = "failed"; s["verifier_timeout"] = True; subs[sid] = s
            print(f"NOTIFY: zkGolf {s['slug']} {sid[:8]} -> failed (VERIFIER TIMEOUT, not a bad solution; "
                  f"claimed {s.get('score')} — worth resubmitting)")
            continue
        if stt in ("verified","failed","error") or score is not None:
            final = "verified" if (stt == "verified" or score is not None) else "failed"
            s["status"] = final; s["is_record"] = r.get("is_record"); subs[sid] = s
            tag = "RECORD! " if r.get("is_record") else ""
            print(f"NOTIFY: zkGolf {s['slug']} {sid[:8]} -> {final} score={score} {tag}(claimed {s.get('score')})")
            # Terminal and not a timeout, so the preserved tree has served its purpose — drop it.
            # Timed-out submissions keep theirs; that copy is the only way to resubmit them.
            keep = os.path.join("out", s["slug"], f"submitted-{sid}.tar.gz")
            try:
                if os.path.exists(keep): os.remove(keep)
            except Exception as e: print(f"STATUS: sub {sid[:8]} prune-error {e}")
    save("state_subs.json", subs)
async def main():
    st0 = load("state_jobs.json", {}); await reconcile_orphans(st0); save("state_jobs.json", st0)
    await process_jobs()
    st = load("state_jobs.json", {}); await ensure_inflight(st); save("state_jobs.json", st)
    process_subs()
if __name__ == "__main__":
    lock = os.path.join(HERE, ".tick.lock")
    try:
        os.close(os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY))
    except FileExistsError:
        import sys
        if time.time() - os.path.getmtime(lock) > 1200: os.remove(lock)
        else: print("STATUS: tick already running"); sys.exit(0)
        os.close(os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY))
    try: asyncio.run(main())
    finally:
        try: os.remove(lock)
        except Exception: pass
