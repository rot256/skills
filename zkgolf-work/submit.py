import asyncio, json, sys, os, datetime, aristotlelib
CHALLENGES=["sha256-hash","keccak-f1600","rsa-pkcs1v15-sha256-4096-65537",
 "secp256k1-scalar-mul","secp256k1-fixed-base-scalar-mul"]
PROMPTDIR=os.environ.get("PROMPTDIR","prompts")
PURPOSE=os.environ.get("PURPOSE","improve-on-record")
KEYNAME=os.environ.get("KEYNAME","primary")
KEY={"primary":os.environ.get("ARISTOTLE_API_KEY"),"alt":os.environ.get("ARISTOTLE_API_KEY_ALT")}[KEYNAME]
os.environ["ARISTOTLE_API_KEY"]=KEY
async def submit_one(slug):
    prompt=open(f"{PROMPTDIR}/{slug}.md").read()
    p=await aristotlelib.Project.create_from_directory(prompt=prompt, project_dir=f"projs/{slug}")
    return slug,p.project_id
async def main():
    slugs=sys.argv[1:] or CHALLENGES
    res=await asyncio.gather(*[submit_one(s) for s in slugs], return_exceptions=True)
    now=datetime.datetime.utcnow().isoformat()+"Z"
    st=json.load(open("state_jobs.json"))
    for r in res:
        if isinstance(r,Exception): print("ERROR:",repr(r)); continue
        slug,pid=r
        st[pid]={"slug":slug,"status":"SUBMITTED","processed":False,"purpose":PURPOSE,"key":KEYNAME,"ts":now}
        with open("jobs.jsonl","a") as f:
            f.write(json.dumps({"ts":now,"slug":slug,"project_id":pid,"purpose":PURPOSE,"key":KEYNAME})+"\n")
        print(f"SUBMITTED {slug} [{PURPOSE}/{KEYNAME}] -> {pid}")
    json.dump(st,open("state_jobs.json","w"),indent=2)
asyncio.run(main())
