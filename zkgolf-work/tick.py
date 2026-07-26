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
SLUG2INST = {"sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
CHALLENGES5 = list(SLUG2INST)
def load(p, d):
    try: return json.load(open(p))
    except Exception: return d
def save(p, o): json.dump(o, open(p, "w"), indent=2)
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
    files = sorted(glob.glob(os.path.join(soldir, "*.lean")), key=lambda f: (0 if f.endswith("Main.lean") else 1, f))
    a = c = None
    for f in files:
        t = open(f, errors="ignore").read()
        if a is None:
            m = re.search(r"def\s+allocations\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t); a = int(m.group(1)) if m else a
        if c is None:
            m = re.search(r"def\s+constraints\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t); c = int(m.group(1)) if m else c
    return a, c
XPOLL_MARK = {  # if the seed's cross-pollinated gadget appears, credit the technique
    "rsa-pkcs1v15-sha256-4096-65537": ("EqViaCarriesFlex", "flexible-limb equality/carry (ported from secp)"),
    "secp256k1-scalar-mul": ("EqViaCarriesFlex", "flexible-limb equality/carry (ported from secp-fixed)"),
    "secp256k1-fixed-base-scalar-mul": ("GroupedEqXV", "XV equality-grouping (ported from secp-mul)"),
}
def describe(slug, score, alloc, constr, best, purpose, soldir):
    parts = [f"{score} = {alloc} alloc + {constr} constr"]
    if best is not None:
        b = int(best); d = int(score) - b
        parts.append(f"({d:+d} vs prev best {b})" if d else f"(matches best {b})")
    tag, note = XPOLL_MARK.get(slug, (None, None))
    if tag and any(tag in os.path.basename(f) for f in glob.glob(os.path.join(soldir, "*.lean"))):
        parts.append(f"via {note}")
    parts.append(f"Aristotle {purpose or 'run'}")
    return " — ".join(parts)
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
            outdir = os.path.join("out", slug); os.makedirs(outdir, exist_ok=True); tarp = os.path.join(outdir, "solution.tar.gz")
            try:
                if not getattr(p, "has_files", True):
                    print(f"NOTIFY: aristotle {slug} produced no files"); j["processed"]=True; st[pid]=j; continue
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
    for slug in CHALLENGES5:
        for purpose, pdir in (("big-win","prompts"), ("small-win","prompts_small")):
            for kname in KEYS_TO_USE:
                if (slug, purpose, kname) in active: continue
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
        if stt in ("verified","failed","error") or score is not None:
            final = "verified" if (stt == "verified" or score is not None) else "failed"
            s["status"] = final; s["is_record"] = r.get("is_record"); subs[sid] = s
            tag = "RECORD! " if r.get("is_record") else ""
            print(f"NOTIFY: zkGolf {s['slug']} {sid[:8]} -> {final} score={score} {tag}(claimed {s.get('score')})")
    save("state_subs.json", subs)
async def main():
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
