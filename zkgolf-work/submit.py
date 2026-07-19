import asyncio, json, sys, datetime, aristotlelib
CHALLENGES=["assert-bytes","sha256-hash","keccak-f1600",
 "rsa-pkcs1v15-sha256-4096-65537","secp256k1-scalar-mul","secp256k1-fixed-base-scalar-mul"]
async def submit_one(slug):
    prompt=open(f"prompts/{slug}.md").read()
    p=await aristotlelib.Project.create_from_directory(prompt=prompt, project_dir=f"projs/{slug}")
    return slug, p.project_id
async def main():
    slugs=sys.argv[1:] or CHALLENGES
    res=await asyncio.gather(*[submit_one(s) for s in slugs], return_exceptions=True)
    now=datetime.datetime.utcnow().isoformat()+"Z"
    try: state=json.load(open("state_jobs.json"))
    except Exception: state={}
    for r in res:
        if isinstance(r,Exception): print("ERROR:",repr(r)); continue
        slug,pid=r
        state[pid]={"slug":slug,"status":"SUBMITTED","processed":False,"purpose":"improve-on-record","ts":now}
        with open("jobs.jsonl","a") as f:
            f.write(json.dumps({"ts":now,"slug":slug,"project_id":pid,"purpose":"improve-on-record","status":"SUBMITTED"})+"\n")
        print(f"SUBMITTED {slug} -> {pid}")
    json.dump(state,open("state_jobs.json","w"),indent=2)
asyncio.run(main())
