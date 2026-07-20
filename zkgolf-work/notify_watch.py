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
                if line.startswith("NOTIFY:"): print(line,flush=True)
        p=subprocess.run(BASE+["tick.py"],capture_output=True,text=True,timeout=900)
        for line in p.stdout.splitlines():
            if line.startswith("NOTIFY:"): print(line,flush=True)
        if p.returncode!=0 and p.stderr.strip():
            print("NOTIFY: tick error: "+p.stderr.strip().splitlines()[-1],flush=True)
    except Exception as e:
        print(f"NOTIFY: watcher exception {e}",flush=True)
    cycles+=1
    time.sleep(INTERVAL)
