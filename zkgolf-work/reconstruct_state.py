#!/usr/bin/env python3
"""Rebuild state_jobs.json from live Aristotle jobs (named by challenge slug). Recovers
job tracking after a restart with no persisted state. Pairs the two jobs per slug as
big-win/small-win (purpose only affects which prompt refills)."""
import os, json, asyncio, aristotlelib
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
SLUGS = {"sha256-hash","keccak-f1600","rsa-pkcs1v15-sha256-4096-65537","secp256k1-scalar-mul","secp256k1-fixed-base-scalar-mul"}
KEYS = {"primary": os.environ.get("ARISTOTLE_API_KEY", "")}
if os.environ.get("ARISTOTLE_API_KEY_ALT"): KEYS["alt"] = os.environ["ARISTOTLE_API_KEY_ALT"]
async def main():
    st = {}; seen = {}
    for kname, kval in KEYS.items():
        os.environ["ARISTOTLE_API_KEY"] = kval
        try:
            projs, _ = await aristotlelib.Project.list_projects(limit=60)
        except Exception as e:
            print(f"{kname}: list error {e}"); continue
        for p in projs:
            if getattr(p.status, "name", str(p.status)) != "RUNNING": continue
            name = (getattr(p, "description", "") or "").strip()
            slug = next((s for s in SLUGS if s in name), None)
            if not slug: continue
            key = (slug, kname); n = seen.get(key, 0); seen[key] = n + 1
            purpose = "big-win" if n == 0 else "small-win"
            st[p.project_id] = {"slug": slug, "purpose": purpose, "status": "RUNNING", "processed": False, "key": kname}
    json.dump(st, open("state_jobs.json", "w"), indent=2)
    print(f"reconstructed {len(st)} running jobs across {list(KEYS)}")
asyncio.run(main())
