#!/usr/bin/env python3
"""One idempotent processing pass for the zkGolf/Aristotle loop.

- Refreshes each Aristotle job; when one COMPLETES, downloads it, extracts the
  Solution files, gates (no sorry, score improved), and auto-submits to zkGolf.
- Polls pending zkGolf submissions; notifies on verified/failed.
- Prints NOTIFY:/STATUS: lines (stdout) so it can run under Monitor.
State: state_jobs.json, state_subs.json (idempotent). Audit: jobs.jsonl, submissions.jsonl.
Run:  ZKGOLF_KEY=.. ARISTOTLE_API_KEY=.. uv run --with aristotlelib --with requests python3 tick.py
"""
import os, re, io, json, glob, time, tarfile, asyncio, datetime, traceback
import requests, aristotlelib

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
ZK = os.environ["ZKGOLF_KEY"]
H = {"Authorization": f"Bearer {ZK}"}
NOW = datetime.datetime.utcnow().isoformat() + "Z"

SLUG2INST = {
    "assert-bytes": "AssertBytes",
    "sha256-hash": "SHA256",
    "keccak-f1600": "KeccakF1600",
    "rsa-pkcs1v15-sha256-4096-65537": "RSASSAPKCS1v15_SHA256_4096_65537",
    "secp256k1-scalar-mul": "Secp256k1ScalarMul",
    "secp256k1-fixed-base-scalar-mul": "Secp256k1ScalarMulFixedBase",
}
# This aristotlelib build reports only RUNNING / IDLE / UNKNOWN.
# IDLE = terminal (Aristotle stopped). Success vs failure is decided by inspecting
# the downloaded output (no `sorry`, parseable cost, improved score) + zkGolf verify.
DONE_TERMINAL = {"IDLE"}
IN_PROGRESS = {"RUNNING", "UNKNOWN"}

def load(p, d):
    try: return json.load(open(p))
    except Exception: return d
def save(p, o): json.dump(o, open(p, "w"), indent=2)
def audit(p, rec):
    with open(p, "a") as f: f.write(json.dumps(rec) + "\n")

def leaderboard_best(slug):
    try:
        lb = requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard", headers=H, timeout=30).json()
        if isinstance(lb, list) and lb: return lb[0]["score"]
    except Exception: pass
    return None

def parse_cost(soldir):
    """Return (alloc, constr) from the Solution files; prefer Main.lean."""
    files = sorted(glob.glob(os.path.join(soldir, "*.lean")))
    files.sort(key=lambda f: (0 if f.endswith("Main.lean") else 1, f))
    a = c = None
    for f in files:
        t = open(f, errors="ignore").read()
        if a is None:
            m = re.search(r"def\s+allocations\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t)
            if m: a = int(m.group(1))
        if c is None:
            m = re.search(r"def\s+constraints\s*:?\s*(?:Nat)?\s*:=\s*(\d+)", t)
            if m: c = int(m.group(1))
    return a, c

def has_holes(soldir):
    for f in glob.glob(os.path.join(soldir, "*.lean")):
        t = open(f, errors="ignore").read()
        for bad in ("sorry", "admit", "native_decide"):
            if re.search(r"\b" + bad + r"\b", t): return bad
    return None

def zk_submit(slug, alloc, constr, desc, files):
    fs = [("artifact", (os.path.basename(f), open(f, "rb"), "text/plain")) for f in files]
    data = {"allocations": str(alloc), "constraints": str(constr),
            "description": desc, "assisted_by": "Aristotle (Harmonic)"}
    r = requests.post(f"https://zk.golf/api/agent/v1/challenges/{slug}/submissions",
                      headers=H, data=data, files=fs, timeout=120)
    return r.status_code, r.text

async def refresh(pid):
    p = await aristotlelib.Project.from_id(pid)
    try: await p.refresh()
    except Exception: pass
    return p

async def process_jobs():
    st = load("state_jobs.json", {})   # pid -> {slug,status,processed,zk_id,...}
    for pid, j in list(st.items()):
        if j.get("processed"):
            continue
        slug = j["slug"]; inst = SLUG2INST[slug]
        try:
            p = await refresh(pid)
        except Exception as e:
            print(f"STATUS: {slug} {pid[:8]} refresh-error {e}"); continue
        status = getattr(p.status, "name", str(p.status))
        j["status"] = status
        if status in DONE_TERMINAL:
            # download + extract
            outdir = os.path.join("out", slug)
            os.makedirs(outdir, exist_ok=True)
            tarp = os.path.join(outdir, "solution.tar.gz")
            try:
                await p.get_solution(destination=tarp)
                with tarfile.open(tarp) as tf: tf.extractall(outdir)
            except Exception as e:
                print(f"STATUS: {slug} download-error {e}"); continue
            soldirs = glob.glob(os.path.join(outdir, "**", "Solution", inst), recursive=True)
            if not soldirs:
                print(f"NOTIFY: aristotle {slug} COMPLETE but no Solution/{inst} in output");
                j["processed"] = True; continue
            soldir = soldirs[0]
            hole = has_holes(soldir)
            alloc, constr = parse_cost(soldir)
            best = leaderboard_best(slug)
            score = (alloc + constr) if (alloc is not None and constr is not None) else None
            j.update({"alloc": alloc, "constr": constr, "score": score, "best": best, "soldir": soldir})
            if hole:
                print(f"NOTIFY: aristotle {slug} {status} but contains `{hole}` — score~{score} vs best {best}; NOT submitting, needs iteration")
                j["processed"] = True; continue
            if score is None:
                print(f"NOTIFY: aristotle {slug} {status}, could not parse alloc/constr — NOT submitting")
                j["processed"] = True; continue
            if best is not None and score >= best:
                print(f"NOTIFY: aristotle {slug} {status} score {score} does NOT beat best {best} — NOT submitting")
                j["processed"] = True; continue
            files = sorted(glob.glob(os.path.join(soldir, "*.lean")))
            code, text = zk_submit(slug, alloc, constr, f"Aristotle-optimized ({score} = {alloc}+{constr})", files)
            try: sid = json.loads(text).get("id")
            except Exception: sid = None
            print(f"NOTIFY: SUBMITTED {slug} score {score} (best {best}) http={code} sub={sid}")
            if sid:
                subs = load("state_subs.json", {})
                subs[sid] = {"slug": slug, "score": score, "alloc": alloc, "constr": constr,
                             "status": "pending", "project_id": pid, "ts": NOW}
                save("state_subs.json", subs)
                audit("submissions.jsonl", subs[sid] | {"submission_id": sid})
                j["zk_id"] = sid
            j["processed"] = True
        else:
            pct = getattr(p, "percent_complete", None)
            print(f"STATUS: aristotle {slug} {status} {pct if pct is not None else ''}")
        st[pid] = j
    save("state_jobs.json", st)

def process_subs():
    subs = load("state_subs.json", {})
    for sid, s in list(subs.items()):
        if s.get("status") in ("verified", "failed"):
            continue
        try:
            r = requests.get(f"https://zk.golf/api/agent/v1/submissions/{sid}", headers=H, timeout=30).json()
        except Exception as e:
            print(f"STATUS: sub {sid[:8]} poll-error {e}"); continue
        stt = r.get("status")
        if stt in ("verified", "failed") or (r.get("score") is not None) or stt in ("error",):
            score = r.get("score"); is_record = r.get("is_record")
            final = "verified" if (stt == "verified" or score is not None) else "failed"
            s["status"] = final; s["result_score"] = score; s["is_record"] = is_record
            subs[sid] = s
            tag = "RECORD! " if is_record else ""
            print(f"NOTIFY: zkGolf {s['slug']} submission {sid[:8]} -> {final} score={score} {tag}(claimed {s.get('score')})")
        else:
            print(f"STATUS: sub {s['slug']} {sid[:8]} {stt} {r.get('queue_status',{})}")
    save("state_subs.json", subs)

async def main():
    await process_jobs()
    process_subs()

if __name__ == "__main__":
    # single-flight lock so the Monitor loop and the 15-min cron never double-submit
    lock = os.path.join(HERE, ".tick.lock")
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.close(fd)
    except FileExistsError:
        import sys
        # stale lock older than 20 min -> steal it
        try:
            if time.time() - os.path.getmtime(lock) > 1200:
                os.remove(lock); fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.close(fd)
            else:
                print("STATUS: tick already running, skip"); sys.exit(0)
        except Exception:
            print("STATUS: tick lock contended, skip"); sys.exit(0)
    try:
        asyncio.run(main())
    finally:
        try: os.remove(lock)
        except Exception: pass
