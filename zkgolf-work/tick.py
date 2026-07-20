#!/usr/bin/env python3
"""zkGolf/Aristotle loop tick. Runtime state is regenerable from the zk.golf + Aristotle
APIs (see bootstrap.sh); only this tooling needs to persist. Location-independent."""
import os, re, json, glob, time, tarfile, asyncio, datetime
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
def zk_submit(slug, alloc, constr, desc, files):
    fs = [("artifact", (os.path.basename(f), open(f, "rb"), "text/plain")) for f in files]
    data = {"allocations": str(alloc), "constraints": str(constr), "description": desc, "assisted_by": "Aristotle (Harmonic)"}
    r = requests.post(f"https://zk.golf/api/agent/v1/challenges/{slug}/submissions", headers=H, data=data, files=fs, timeout=120)
    return r.status_code, r.text
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
            if hole: print(f"NOTIFY: aristotle {slug} contains `{hole}` (score~{score} vs {best}); NOT submitting"); j["processed"]=True; st[pid]=j; continue
            miss = missing_required(soldir)
            if miss: print(f"NOTIFY: aristotle {slug} MISSING {miss} — NOT submitting"); j["processed"]=True; st[pid]=j; continue
            if score is None: print(f"NOTIFY: aristotle {slug} unparseable cost"); j["processed"]=True; st[pid]=j; continue
            if best is not None and score >= best: print(f"NOTIFY: aristotle {slug} score {score} does NOT beat best {best} — NOT submitting"); j["processed"]=True; st[pid]=j; continue
            files = sorted(glob.glob(os.path.join(soldir, "*.lean")))
            code, text = zk_submit(slug, alloc, constr, f"Aristotle-optimized ({score}={alloc}+{constr})", files)
            try: sid = json.loads(text).get("id")
            except Exception: sid = None
            print(f"NOTIFY: SUBMITTED {slug} score {score} (best {best}) http={code} sub={sid}")
            if sid:
                subs = load("state_subs.json", {}); subs[sid] = {"slug": slug, "score": score, "status": "pending", "ts": NOW}
                save("state_subs.json", subs); audit("submissions.jsonl", subs[sid] | {"submission_id": sid}); j["zk_id"] = sid
            j["processed"] = True
        else:
            print(f"STATUS: aristotle {slug} {status}")
        st[pid] = j
    save("state_jobs.json", st)
COOLDOWN_S = 240  # min seconds between re-dispatches of the same (slug,purpose) slot (keep pushing)
async def ensure_inflight(st):
    active = set((j["slug"], j.get("purpose")) for j in st.values() if not j.get("processed"))
    cd = load("cooldown.json", {}); now = time.time()
    for slug in CHALLENGES5:
        for purpose, pdir in (("big-win","prompts"), ("small-win","prompts_small")):
            if (slug, purpose) in active: continue
            key = f"{slug}|{purpose}"
            if now - cd.get(key, 0) < COOLDOWN_S:
                continue  # slot recently dispatched — avoid rapid-fire churn
            try:
                use_key("primary"); prompt = open(f"{pdir}/{slug}.md").read()
                p = await aristotlelib.Project.create_from_directory(prompt=prompt, project_dir=f"projs/{slug}")
                st[p.project_id] = {"slug": slug, "status": "SUBMITTED", "processed": False, "purpose": purpose, "key": "primary", "ts": NOW}
                cd[key] = now; save("cooldown.json", cd)
                print(f"NOTIFY: auto-dispatched {slug} [{purpose}] -> {p.project_id}")
            except Exception as e:
                print(f"STATUS: refill {slug}/{purpose} failed {e}")
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
