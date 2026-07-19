import sys, requests, os
KEY=os.environ["ZKGOLF_KEY"]
slug, alloc, constr, desc = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
files = [("artifact", (os.path.basename(f), open(f,"rb"), "text/plain")) for f in sys.argv[5:]]
data = {"allocations": alloc, "constraints": constr, "description": desc, "assisted_by": "Aristotle (Harmonic)"}
r = requests.post(f"https://zk.golf/api/agent/v1/challenges/{slug}/submissions",
                  headers={"Authorization": f"Bearer {KEY}"}, data=data, files=files)
print(r.status_code, r.text)
