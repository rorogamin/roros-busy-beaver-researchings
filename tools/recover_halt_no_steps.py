import json
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

CODE = "/content/quicksim-62f9c/Code"
QUICKSIM = CODE + "/Quick_Sim.py"
FLAGS = [
    "-q",
    "--recursive",
    "--print-full-result",
    "--max-loops=2000000",
    "--max-steps-in-block=50000000",
    "--max-steps-in-backsymbol=5000000",
    "--max-block-size=250",
    "--block-mult=4",
    "--max-block-mult=5",
    "--bf-loops=50000",
    "--max-prover-configs=500000",
    "--max-num-reps=100",
]
STEPS_RE = re.compile(r"Steps:\s+[^\n]*?\(([\d_,]+)\)")

rows = []
with open("/content/attempts.jsonl", encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if r.get("status") == "HALT_NO_STEPS":
            rows.append(r)

def run_one(r):
    started = time.time()
    try:
        p = subprocess.run(
            [sys.executable, QUICKSIM, *FLAGS, r["spec"]],
            cwd=CODE,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60,
        )
        out = (p.stdout or "") + "\n" + (p.stderr or "")
        rc = p.returncode
        timed_out = False
    except subprocess.TimeoutExpired as e:
        out = ""
        for s in (e.stdout, e.stderr):
            if s:
                out += s if isinstance(s, str) else s.decode("utf-8", "replace")
        rc = None
        timed_out = True
    matches = STEPS_RE.findall(out)
    steps = matches[-1].replace("_", "").replace(",", "") if matches else None
    if "Turing Machine Halted" in out and steps:
        status = "HALT_RECOVERED"
    elif "Turing Machine Halted" in out:
        status = "HALT_STILL_NO_STEPS"
    elif timed_out:
        status = "TIMEOUT"
    else:
        status = "OTHER"
    return {
        "idx": r["idx"],
        "spec": r["spec"],
        "status": status,
        "steps_exact": steps,
        "steps_digits": len(steps) if steps else None,
        "elapsed": round(time.time() - started, 3),
        "rc": rc,
        "timed_out": timed_out,
        "tail": "\n".join(out.splitlines()[-5:]),
    }

results = []
with ThreadPoolExecutor(max_workers=6) as ex:
    futs = {ex.submit(run_one, r): r for r in rows}
    for fut in as_completed(futs):
        results.append(fut.result())
results.sort(key=lambda x: x["idx"])
print("TRIAGE", len(results))
for r in results:
    print(json.dumps(r, ensure_ascii=False))
with open("/content/halt_no_steps_recovered.jsonl", "w", encoding="utf-8") as f:
    for r in results:
        f.write(json.dumps(r) + "\n")
print("wrote /content/halt_no_steps_recovered.jsonl")
