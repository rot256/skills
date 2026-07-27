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
    d=f"records/{slug}"; os.makedirs(d,exist_ok=True)
    for f in glob.glob(d+"/*.lean"): os.remove(f)
    try:
        with tarfile.open(fileobj=io.BytesIO(requests.get(f"https://zk.golf/api/submissions/{sid}/download",headers=H,timeout=90).content)) as tf: tf.extractall(d)
    except Exception as e: print(f"{slug}: extract err {e}"); continue
    files=glob.glob(d+"/*.lean")
    if not any("computableWitness" in open(f,errors="ignore").read() for f in files):
        print(f"{slug}: new best {new} by {t['github_login']} lacks computableWitness — not reseeding"); continue
    soldir=f"projs/{slug}/Solution/{inst}"
    for f in glob.glob(soldir+"/*.lean"): os.remove(f)
    for f in files: shutil.copy(f, soldir)
    for pf in (f"prompts/{slug}.md", f"prompts_small/{slug}.md"):
        if os.path.exists(pf):
            c = open(pf).read()            # read FIRST (never truncate-before-read)
            if c.strip():                  # never blank out a prompt
                open(pf, "w").write(c.replace(str(old), str(new)))
    tg[slug]={"target":new,"seed":f"valid record {new} by {t['github_login']}","by":t["github_login"]}
    changed.append((slug,old,new,t["github_login"]))
json.dump(tg,open("targets.json","w"),indent=2)
# NOTE: never cancel in-flight jobs. When a record moves we only re-seed projs + update
# targets/prompts for FUTURE dispatches; running jobs finish on their own and the tick gate
# re-evaluates their output against the new best.
for slug,o,n,by in changed: print(f"NOTIFY: record moved {slug} {o}->{n} (by {by}); re-seeded (running jobs left to finish)")
