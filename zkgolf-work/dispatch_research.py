#!/usr/bin/env python3
"""One-shot Aristotle dispatch for a standalone Lean proof obligation.

Deliberately does NOT touch state_jobs.json or the SLOTS machinery: the fleet's state
file is shared with the watcher and the keepalive procedure forbids concurrent writers.
Research jobs are tracked separately in state_research.json so they can be polled
without any risk to the record-hunting loop.
"""
import asyncio, json, os, sys, datetime, aristotlelib

STATE = "state_research.json"

async def main(name):
    d = f"research/{name}"
    prompt = open(f"{d}/PROMPT.md").read()
    assert prompt.strip(), "empty prompt"
    p = await aristotlelib.Project.create_from_directory(prompt=prompt, project_dir=d)
    st = json.load(open(STATE)) if os.path.exists(STATE) else {}
    st[p.project_id] = {"name": name, "dir": d, "status": "SUBMITTED", "processed": False,
                        "ts": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    json.dump(st, open(STATE, "w"), indent=2)
    print(f"NOTIFY: research job dispatched {name} -> {p.project_id}")

asyncio.run(main(sys.argv[1]))
