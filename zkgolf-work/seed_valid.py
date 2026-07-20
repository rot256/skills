#!/usr/bin/env python3
"""Seed projs/<slug>/Solution/<inst> from the valid best record (baseline if the best
lacks computableWitness); write targets.json. Location-independent."""
import requests, os, json, tarfile, glob, io, shutil
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
KEY=os.environ["ZKGOLF_KEY"]; H={"Authorization":f"Bearer {KEY}"}
INST={"sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
targets={}
for slug,inst in INST.items():
    lb=requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard",headers=H,timeout=30).json()
    t=min(lb,key=lambda e:e["score"]); sid=t["submission_id"]; score=int(t["score"])
    d=f"records/{slug}"; os.makedirs(d,exist_ok=True)
    for f in glob.glob(d+"/*.lean"): os.remove(f)
    with tarfile.open(fileobj=io.BytesIO(requests.get(f"https://zk.golf/api/submissions/{sid}/download",headers=H,timeout=90).content)) as tf: tf.extractall(d)
    files=glob.glob(d+"/*.lean")
    cw=any("computableWitness" in open(f,errors="ignore").read() for f in files)
    soldir=f"projs/{slug}/Solution/{inst}"; os.makedirs(soldir,exist_ok=True)
    for f in glob.glob(soldir+"/*.lean"): os.remove(f)
    if cw:
        for f in files: shutil.copy(f, soldir); seed=f"valid record {score} by {t['github_login']}"
    else:
        for f in glob.glob(f"zk-golf-challenges/Solution/{inst}/*.lean"): shutil.copy(f, soldir)
        seed=f"baseline (record {score} lacks cw)"
    targets[slug]={"target":score,"seed":seed,"by":t["github_login"]}
    print(f"{slug}: target<{score} seed={seed} ({len(glob.glob(soldir+'/*.lean'))} files)")
json.dump(targets,open("targets.json","w"),indent=2)
