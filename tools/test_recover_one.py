import subprocess
import sys
import time

spec = "1RB1RA_1RC0RB_1LC0RD_1RZ0RE_1LF0LA_1LE1LG_1LA1RB"
code = "/content/quicksim-62f9c/Code"
quicksim = code + "/Quick_Sim.py"
flags = [
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
started = time.time()
try:
    p = subprocess.run(
        [sys.executable, quicksim, *flags, spec],
        cwd=code,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=60,
    )
    out = (p.stdout or "") + "\n" + (p.stderr or "")
    print("rc", p.returncode, "elapsed", round(time.time() - started, 3))
    print(out[-5000:])
except subprocess.TimeoutExpired as e:
    out = ""
    for s in (e.stdout, e.stderr):
        if s:
            out += s if isinstance(s, str) else s.decode("utf-8", "replace")
    print("TIMEOUT elapsed", round(time.time() - started, 3))
    print(out[-5000:])
