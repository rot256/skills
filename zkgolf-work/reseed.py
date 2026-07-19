import os, json, glob, tarfile, requests
KEY=os.environ["ZKGOLF_KEY"]; H={"Authorization": f"Bearer {KEY}"}
SLUG2INST={"assert-bytes":"AssertBytes","sha256-hash":"SHA256","keccak-f1600":"KeccakF1600",
 "rsa-pkcs1v15-sha256-4096-65537":"RSASSAPKCS1v15_SHA256_4096_65537",
 "secp256k1-scalar-mul":"Secp256k1ScalarMul","secp256k1-fixed-base-scalar-mul":"Secp256k1ScalarMulFixedBase"}
info={}
for slug,inst in SLUG2INST.items():
    lb=requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard",headers=H,timeout=30).json()
    if not (isinstance(lb,list) and lb):
        print(f"{slug}: NO leaderboard entry"); continue
    top=lb[0]; sid=top["submission_id"]; score=top["score"]
    recdir=f"records/{slug}"; os.makedirs(recdir,exist_ok=True)
    tp=f"{recdir}/rec.tar.gz"
    r=requests.get(f"https://zk.golf/api/submissions/{sid}/download",headers=H,timeout=60)
    open(tp,"wb").write(r.content)
    # clean prior extracted
    for f in glob.glob(f"{recdir}/*.lean"): os.remove(f)
    with tarfile.open(tp) as tf: tf.extractall(recdir)
    leans=glob.glob(f"{recdir}/*.lean")
    # stage into projs/<slug>/Solution/<inst>/
    soldir=f"projs/{slug}/Solution/{inst}"
    for f in glob.glob(f"{soldir}/*.lean"): os.remove(f)
    os.makedirs(soldir,exist_ok=True)
    for f in leans:
        os.replace(f, os.path.join(soldir, os.path.basename(f)))
    info[slug]={"record_sid":sid,"record_score":score,"by":top["github_login"],
                "n_files":len(leans),"staged":sorted(os.path.basename(x) for x in glob.glob(f"{soldir}/*.lean"))}
    print(f"{slug}: record {score} by {top['github_login']} -> staged {len(leans)} files into {soldir}")
json.dump(info,open("records/info.json","w"),indent=2)
