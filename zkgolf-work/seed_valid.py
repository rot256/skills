#!/usr/bin/env python3
"""Seed projs/<slug>/Solution/<inst> from the valid best record (baseline if the best
lacks computableWitness); write targets.json. Location-independent."""
import requests, os, json, tarfile, glob, io, shutil
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
KEY=os.environ["ZKGOLF_KEY"]; H={"Authorization":f"Bearer {KEY}"}
INST={"gf2-k12-compress-canonical":"KangarooTwelveGF2","gf2-sha256-compress-canonical":"SHA256CompressGF2Canonical","sha256-hash":"SHA256","keccak-f1600":"KeccakF1600","rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537","secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
targets={}
CHS={c["slug"]:c for c in requests.get("https://zk.golf/api/agent/v1/challenges",headers=H,timeout=30).json()}
for slug,inst in INST.items():
    lb=requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard",headers=H,timeout=30).json()
    if not lb:
        # No submissions yet: seed from the challenge baseline and target its baseline_score.
        score=int(CHS[slug]["baseline_score"])
        soldir=f"projs/{slug}/Solution/{inst}"; os.makedirs(soldir,exist_ok=True)
        for f in glob.glob(soldir+"/*.lean"): os.remove(f)
        for f in glob.glob(f"zk-golf-challenges/Solution/{inst}/*.lean"): shutil.copy(f, soldir)
        # AN EMPTY LEADERBOARD DOES NOT MEAN NOBODY HAS SUBMITTED. The leaderboard lists only
        # entries that STRICTLY BEAT the baseline, so a verified submission that TIES it is
        # accepted, marked is_record, and still shows nothing here. gf2-k12 is exactly that case:
        # rot256 submitted 38400 on 2026-07-28, it verified, and the leaderboard is []. Writing
        # "NO submissions yet — first valid entry takes the record" then manufactured a phantom
        # free record that got re-investigated at least twice. Distinguish the two by comparing
        # against baseline_score.
        tied = int(CHS[slug].get("best_score") or 0) == score
        note = (f"baseline {score} (TIED by a verified submission — a tie does not rank, so beating "
                f"it needs a STRICT improvement)" if tied else
                f"baseline {score} (no ranking submission yet)")
        targets[slug]={"target":score,"seed":note,"by":None}
        print(f"{slug}: target<{score} seed=baseline {'TIED' if tied else 'UNRANKED'} "
              f"({len(glob.glob(soldir+'/*.lean'))} files)")
        continue
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
