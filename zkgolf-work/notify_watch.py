#!/usr/bin/env python3
"""Persistent poller: runs one tick.py pass every WATCH_INTERVAL seconds and
forwards only NOTIFY: lines (terminal transitions — submissions, verify results,
records, failures). Designed to run under the Monitor tool so success/failure
wakes the loop. tick.py is idempotent, so each event notifies exactly once.
"""
import subprocess, time, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
INTERVAL = int(os.environ.get("WATCH_INTERVAL", "180"))
CMD = ["uv","run","--with","aristotlelib","--with","requests","python3","tick.py"]
while True:
    try:
        p = subprocess.run(CMD, capture_output=True, text=True, timeout=900)
        for line in p.stdout.splitlines():
            if line.startswith("NOTIFY:"):
                print(line, flush=True)
        if p.returncode != 0 and p.stderr.strip():
            print("NOTIFY: tick error: " + p.stderr.strip().splitlines()[-1], flush=True)
    except Exception as e:
        print(f"NOTIFY: watcher exception {e}", flush=True)
    time.sleep(INTERVAL)
