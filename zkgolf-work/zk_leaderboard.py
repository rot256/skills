import requests, os, json, sys
KEY=os.environ["ZKGOLF_KEY"]; H={"Authorization": f"Bearer {KEY}"}
slugs=["assert-bytes","sha256-hash","keccak-f1600","rsa-pkcs1v15-sha256-4096-65537","secp256k1-scalar-mul","secp256k1-fixed-base-scalar-mul"]
BASE={"assert-bytes":272,"sha256-hash":413810,"keccak-f1600":307200,"rsa-pkcs1v15-sha256-4096-65537":827136,"secp256k1-scalar-mul":16462088,"secp256k1-fixed-base-scalar-mul":16462088}
out={}
for s in slugs:
    try:
        lb=requests.get(f"https://zk.golf/api/agent/v1/challenges/{s}/leaderboard",headers=H,timeout=30).json()
    except Exception as e:
        out[s]={"error":str(e)}; continue
    if isinstance(lb,list) and lb:
        t=lb[0]
        out[s]={"best":t["score"],"by":t["github_login"],"alloc":t["allocations"],"constr":t["constraints"],"baseline":BASE[s]}
    else:
        out[s]={"best":None,"by":None,"baseline":BASE[s],"raw":lb if not isinstance(lb,list) else "empty"}
json.dump(out,open("leaderboard.json","w"),indent=2)
print(json.dumps(out,indent=2))
