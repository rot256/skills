#!/usr/bin/env python3
"""Detect competitor record improvements; re-seed projs from the new VALID best."""
import requests, os, json, tarfile, glob, io, shutil, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
KEY=os.environ["ZKGOLF_KEY"]; H={"Authorization":f"Bearer {KEY}"}
INST={"gf2-k12-compress-canonical":"KangarooTwelveGF2","gf2-sha256-compress-canonical":"SHA256CompressGF2Canonical","sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
try: tg=json.load(open("targets.json"))
except Exception: tg={}
if not tg: print("STATUS: no targets"); raise SystemExit(0)
# best_score is None for challenges with no submissions yet (unclaimed) — keep them, never int(None)
chs={c["slug"]:c["best_score"] for c in requests.get("https://zk.golf/api/agent/v1/challenges",headers=H,timeout=30).json() if c["slug"] in tg}
changed=[]
for slug,inst in INST.items():
    if slug not in tg: continue
    new=chs.get(slug); old=tg[slug]["target"]
    if new is None: continue          # unclaimed challenge: nothing to re-seed from
    new=int(new)
    if new>=old: continue
    lb=requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard",headers=H,timeout=30).json()
    t=min(lb,key=lambda e:e["score"]); new=int(t["score"]); sid=t["submission_id"]
    # The leaderboard lags the challenges endpoint. When it does, its minimum is an OLDER, WORSE
    # tree than the authoritative best — and reseeding from it silently handicaps every job for
    # that slug. Measured: for hours the leaderboard's best was 317180 while best_score was
    # 316436, so projs/ was re-seeded from the 744-worse tree on every single tick. Skip until
    # the leaderboard catches up; targets.json is left alone so we retry next tick.
    if new > int(chs[slug]):
        print(f"{slug}: leaderboard stale (best {new}, challenges says {int(chs[slug])}) — not reseeding"); continue
    d=f"records/{slug}"; os.makedirs(d,exist_ok=True)
    for f in glob.glob(d+"/*.lean"): os.remove(f)
    try:
        with tarfile.open(fileobj=io.BytesIO(requests.get(f"https://zk.golf/api/submissions/{sid}/download",headers=H,timeout=90).content)) as tf: tf.extractall(d)
    except Exception as e: print(f"{slug}: extract err {e}"); continue
    files=glob.glob(d+"/*.lean")
    if not any("computableWitness" in open(f,errors="ignore").read() for f in files):
        print(f"{slug}: new best {new} by {t['github_login']} lacks computableWitness — not reseeding"); continue
    soldir=f"projs/{slug}/Solution/{inst}"
    # ARCHIVE THE OUTGOING TREE FIRST. It is about to be deleted, and when a rival takes the
    # record the tree being deleted is OUR last verified one -- a different lineage that is known
    # to elaborate inside the verifier budget, which is exactly what a timing-out slug needs to
    # compare against. Stored .lean.txt under reference/ so jobs read it as context and never
    # compile it, matching the rival-<author>-<score> convention. Only the most recent snapshot is
    # kept, so this costs one tree of disk per slug and never grows.
    try:
        prev = sorted(glob.glob(soldir+"/*.lean"))
        if prev:
            pdir = f"projs/{slug}/reference/prev-{old}"
            for stale in glob.glob(f"projs/{slug}/reference/prev-*"):
                if stale != pdir: shutil.rmtree(stale, ignore_errors=True)
            os.makedirs(pdir, exist_ok=True)
            for f in prev: shutil.copy(f, os.path.join(pdir, os.path.basename(f)+".txt"))
            open(os.path.join(pdir,"MANIFEST.txt"),"w").write(
                f"score {old}\nheld_by {tg[slug].get('by')}\nreplaced_by {t['github_login']} at {new}\n"
                f"This is the tree that held the record immediately before the current seed. If it was\n"
                f"ours it is known to VERIFY, i.e. to fit the elaboration budget -- useful when the\n"
                f"current seed keeps timing out. Context only; not compiled.\n")
            print(f"NOTIFY: archived outgoing {slug} tree @{old} -> reference/prev-{old} ({len(prev)} files)")
    except Exception as e:
        print(f"NOTIFY: could not archive outgoing {slug} tree: {e}")
    for f in glob.glob(soldir+"/*.lean"): os.remove(f)
    for f in files: shutil.copy(f, soldir)
    # DO NOT rewrite prompt text here. A blind old->new replace also hits the workqueue header's
    # `derived` value, which is a claim about WHEN the items were worked out, not a copy of the
    # live score -- rewriting it silences the `now != derived` staleness banner and makes stale
    # items read as freshly derived. Prompts are regenerated from targets.json below instead.
    tg[slug]={"target":new,"seed":f"valid record {new} by {t['github_login']}","by":t["github_login"]}
    changed.append((slug,old,new,t["github_login"]))
json.dump(tg,open("targets.json","w"),indent=2)
if changed:
    # Regenerate prompts from the new targets.json. gen_prompts.py is the only place that knows
    # which numbers are live (the target, the seed's real cost) and which are historical claims
    # (the workqueue's `derived`), so it is the only thing allowed to write a prompt.
    try:
        r = subprocess.run(["python3", "gen_prompts.py"], capture_output=True, text=True, timeout=300)
        if r.returncode != 0:
            print("NOTIFY: gen_prompts FAILED after reseed: " + (r.stderr.strip().splitlines() or ["?"])[-1])
        else:
            for line in r.stdout.splitlines():
                if line.startswith(("SEED DIVERGENCE", "WARN")): print("NOTIFY: " + line)
    except Exception as e:
        print(f"NOTIFY: gen_prompts could not run after reseed: {e}")
# NOTE: never cancel in-flight jobs. When a record moves we only re-seed projs + update
# targets/prompts for FUTURE dispatches; running jobs finish on their own and the tick gate
# re-evaluates their output against the new best.
for slug,o,n,by in changed: print(f"NOTIFY: record moved {slug} {o}->{n} (by {by}); re-seeded (running jobs left to finish)")
