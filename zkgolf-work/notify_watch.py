#!/usr/bin/env python3
"""Persistent poller: check_records (~every 4th cycle) + tick each cycle; forward NOTIFY lines.
Run under the Monitor tool. Location-independent."""
import subprocess, time, os
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE)
INTERVAL=int(os.environ.get("WATCH_INTERVAL","180"))
BASE=["uv","run","--with","aristotlelib","--with","requests","python3"]
cycles=0
while True:
    try:
        if cycles % 4 == 0:
            c=subprocess.run(BASE+["check_records.py"],capture_output=True,text=True,timeout=600)
            for line in c.stdout.splitlines():
                if line.startswith("NOTIFY:") and any(k in line for k in ("SUBMITTED","verified","failed","RECORD","record moved","adopted")): print(line,flush=True)
            if c.returncode!=0 and c.stderr.strip():
                # a crash here silently kills record detection — surface it
                print("NOTIFY: check_records FAILED: "+c.stderr.strip().splitlines()[-1],flush=True)
        if cycles % 30 == 0:
            # Harvest competitors' submissions into projs/<slug>/reference/ so we are not stuck in
            # our own lineage. Rare (leaderboards move slowly) and non-fatal: a failure here must
            # never stop the tick, which is what actually dispatches and submits.
            try:
                o=subprocess.run(BASE+["pull_others.py"],capture_output=True,text=True,timeout=900)
                for line in o.stdout.splitlines():
                    if line.startswith("NOTIFY:"): print(line,flush=True)
            except Exception as e:
                print(f"NOTIFY: pull_others failed {e}",flush=True)
        p=subprocess.run(BASE+["tick.py"],capture_output=True,text=True,timeout=900)
        for line in p.stdout.splitlines():
            if line.startswith("NOTIFY:") and any(k in line for k in ("SUBMITTED","verified","failed","RECORD","record moved","adopted")): print(line,flush=True)
            # a refill that keeps failing drains the fleet silently — STATUS lines were never forwarded.
            # "too many projects in progress" is the per-key RUNNING cap, i.e. a FULL fleet: expected, not a fault.
            elif line.startswith("STATUS: refill") and "failed" in line and "too many projects in progress" not in line:
                print("NOTIFY: "+line,flush=True)
        if p.returncode!=0 and p.stderr.strip():
            print("NOTIFY: tick error: "+p.stderr.strip().splitlines()[-1],flush=True)
    except Exception as e:
        print(f"NOTIFY: watcher exception {e}",flush=True)
    cycles+=1
    time.sleep(INTERVAL)
