import sys, requests, os
KEY=os.environ["ZKGOLF_KEY"]
r=requests.get(f"https://zk.golf/api/agent/v1/submissions/{sys.argv[1]}",
               headers={"Authorization": f"Bearer {KEY}"})
print(r.text)
