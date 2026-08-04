#!/usr/bin/env python3
"""Harvest COMPETITORS' submissions into projs/<slug>/reference/rival-<login>-<score>/.

check_records.py already reseeds projs/<slug>/Solution/ from whoever currently holds the
record — including competitors — so we are never stuck on our own lineage for the #1 entry.
Two gaps it does not cover, which this closes:

  1. It only ever pulls the #1 entry. A rival sitting at #2 with a technique we lack is
     invisible, however good the idea is.
  2. On a slug where WE hold the record it pulls nothing at all, so we see no one else's work.

So: for each slug take the BEST submission from each distinct rival author, download it, and
stage it as reference material (.lean.txt, context-only, never compiled — same convention as
the existing cross-pollination reference/ files). Solutions worse than ours are still worth
reading: the score is a sum over the whole circuit, and a worse total can still contain a
better gadget.

Idempotent: a rival's submission is re-fetched only when their best changes.
"""
import requests, os, json, tarfile, io, glob, shutil

HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
KEY = os.environ["ZKGOLF_KEY"]; H = {"Authorization": f"Bearer {KEY}"}
US = os.environ.get("ZKGOLF_LOGIN", "rot256")
MAX_RIVALS = int(os.environ.get("MAX_RIVALS", "1"))   # per slug; each is a whole solution tree (~3-5MB)
MAX_FILES = int(os.environ.get("MAX_RIVAL_FILES", "400"))  # skip absurdly large trees
SLUGS = ["gf2-k12-compress-canonical", "gf2-sha256-compress-canonical", "sha256-hash",
         "keccak-f1600", "rsa-pkcs1v15-sha256-4096-65537", "secp256k1-scalar-mul",
         "secp256k1-fixed-base-scalar-mul"]
STATE = "state_others.json"

def load(p, d):
    try: return json.load(open(p))
    except Exception: return d
def save(p, o):
    tmp = p + ".tmp"
    with open(tmp, "w") as f:
        json.dump(o, f, indent=2); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, p)

st = load(STATE, {})
changed = False

for slug in SLUGS:
    try:
        lb = requests.get(f"https://zk.golf/api/agent/v1/challenges/{slug}/leaderboard",
                          headers=H, timeout=30).json()
    except Exception as e:
        print(f"STATUS: pull_others {slug} leaderboard failed {e}"); continue
    if not isinstance(lb, list) or not lb: continue

    # Best entry per distinct rival author, cheapest first — but SKIP THE CURRENT RECORD HOLDER.
    # When a rival holds the record, check_records.py has already reseeded projs/<slug>/Solution/
    # from exactly that submission, so staging it again under reference/ would ship the same tree
    # twice and double the upload for nothing. We want the people we are NOT already learning from.
    order = sorted(lb, key=lambda z: z["score"])
    holder = order[0].get("github_login") if order else None
    best = {}
    for e in order:
        who = e.get("github_login")
        if not who or who == US or who == holder: continue
        best.setdefault(who, e)
    rivals = list(best.values())[:MAX_RIVALS]
    if not rivals: continue

    refdir = f"projs/{slug}/reference"
    os.makedirs(refdir, exist_ok=True)
    keep = set()
    for e in rivals:
        who, score, sid = e["github_login"], int(e["score"]), e["submission_id"]
        dst = f"{refdir}/rival-{who}-{score}"
        keep.add(os.path.basename(dst))
        if st.get(f"{slug}/{who}") == sid and os.path.isdir(dst):
            continue                                  # already have this exact submission
        try:
            blob = requests.get(f"https://zk.golf/api/submissions/{sid}/download",
                                headers=H, timeout=90).content
            with tarfile.open(fileobj=io.BytesIO(blob)) as tf:
                members = [m for m in tf.getmembers() if m.isfile() and m.name.endswith(".lean")]
                if len(members) > MAX_FILES:
                    print(f"STATUS: pull_others {slug} {who}@{score} has {len(members)} files > {MAX_FILES}, skipping")
                    keep.discard(os.path.basename(dst)); continue
                shutil.rmtree(dst, ignore_errors=True); os.makedirs(dst, exist_ok=True)
                for m in members:
                    data = tf.extractfile(m).read()
                    # .lean.txt so lake never tries to build it; flatten to avoid path escapes
                    open(os.path.join(dst, os.path.basename(m.name) + ".txt"), "wb").write(data)
            open(f"{dst}/MANIFEST.txt", "w").write(
                f"zk.golf submission by {who}\nchallenge: {slug}\nscore: {score}\n"
                f"submission_id: {sid}\nfiles: {len(members)}\n\n"
                "Context only — NOT compiled, NOT part of our Solution. Read it for gadgets or\n"
                "structural ideas our solution lacks. A worse TOTAL can still hide a better part.\n")
            st[f"{slug}/{who}"] = sid; changed = True
            print(f"NOTIFY: pulled rival solution {slug} {who}@{score} ({len(members)} files)")
        except Exception as ex:
            print(f"STATUS: pull_others {slug} {who}@{score} download failed {ex}")
    # drop superseded rival dirs so the project does not accumulate stale trees
    for d in glob.glob(f"{refdir}/rival-*"):
        if os.path.basename(d) not in keep:
            shutil.rmtree(d, ignore_errors=True); changed = True
            print(f"STATUS: pull_others dropped stale {d}")

if changed: save(STATE, st)
print("STATUS: pull_others done")
