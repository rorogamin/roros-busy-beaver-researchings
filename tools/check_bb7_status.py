import collections
import json
import os
import re
import subprocess
import time

def run(cmd):
    p = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    return p.stdout.strip() or p.stderr.strip()

print("UTC", time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
for path in ("/content/attempts.jsonl", "/content/run.log"):
    if os.path.exists(path):
        st = os.stat(path)
        print(f"FILE {path} bytes={st.st_size} mtime={time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(st.st_mtime))}")
    else:
        print(f"FILE {path} MISSING")

ps = run("ps -eo pid,etime,pcpu,args | grep -E 'run_haulters_quicksim|Quick_Sim' | grep -v grep")
print("--- runners/workers ---")
print(ps)
print("workers=", sum("Quick_Sim.py" in line for line in ps.splitlines()))

rows = []
if os.path.exists("/content/attempts.jsonl"):
    with open("/content/attempts.jsonl", "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            try:
                rows.append(json.loads(line))
            except Exception:
                pass
counts = collections.Counter(r.get("status") for r in rows)
print("--- attempts ---")
print("rows", len(rows), "last_idx", max((r.get("idx", 0) for r in rows), default=0), "counts", dict(counts))

log = run("tail -n 80 /content/run.log")
print("--- last progress ---")
for line in log.splitlines():
    if re.search(r"\[\d+/31415\]", line):
        print(line)
