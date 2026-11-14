#!/usr/bin/env python3
"""Run the newest bundled QuickSim over haulters_pseudoholdouts_31415.txt.

Each input line is one 7-state, 2-symbol machine.  The output is one JSONL
attempt per line (append-only, so an interrupted run can be resumed).  The
"Steps:" value is parsed from QuickSim's final parenthesised exact integer.

This script does not modify the vendored QuickSim sources.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] if len(HERE.parents) > 1 else HERE
DEFAULT_INPUT = Path(r"C:\Users\Rowan\Downloads\haulters_pseudoholdouts_31415.txt")
QUICKSIM = ROOT / "bbwork" / "vendor" / "quicksim-62f9c" / "Code" / "Quick_Sim.py"

# Exact integer printed after the approximate formula on QuickSim's Steps line.
STEPS_RE = re.compile(r"Steps:\s+[^\n]*?\(([\d_,]+)\)")
NONZEROS_RE = re.compile(r"Num Nonzeros:\s+[^\n]*?\(([\d_,]+)\)")

STRONG = [
    "-q",
    "--recursive",
    "--exp-linear-rules",
    "--exp-meta-linear-rules",
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


def load_specs(path: Path) -> list[str]:
    specs = []
    for raw in path.read_text(encoding="utf-8-sig").splitlines():
        spec = raw.strip()
        if spec and not spec.startswith("#"):
            specs.append(spec)
    return specs


def classify(out: str, timed_out: bool) -> str:
    if "Turing Machine Halted" in out:
        return "HALT"
    if "Turing Machine reached Undefined transition" in out:
        return "HALT"
    if "Turing Machine proven Infinite" in out:
        return "INF"
    if timed_out:
        return "TIMEOUT"
    if "Maximum number of loops" in out:
        return "LOOP_LIMIT"
    if "Expression too complex" in out:
        return "EXPR_TOO_COMPLEX"
    if "Over base steps in a single Macro step" in out:
        return "OVER_STEPS"
    return "ERROR"


def parse_exact(regex: re.Pattern[str], out: str) -> str | None:
    matches = regex.findall(out)
    if not matches:
        return None
    value = matches[-1].replace("_", "").replace(",", "")
    return value or None


def run_one(idx: int, spec: str, args: argparse.Namespace) -> dict:
    quicksim = args.quicksim
    cmd = [sys.executable, str(quicksim), *STRONG, spec]
    started = time.time()
    out = ""
    timed_out = False
    rc = None
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(quicksim.parent),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=args.timeout,
        )
        out = (proc.stdout or "") + "\n" + (proc.stderr or "")
        rc = proc.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        for stream in (exc.stdout, exc.stderr):
            if stream:
                out += stream.decode(errors="replace") if isinstance(stream, bytes) else stream
    elapsed = time.time() - started

    status = classify(out, timed_out)
    steps_exact = parse_exact(STEPS_RE, out)
    nonzeros_exact = parse_exact(NONZEROS_RE, out)
    # A halt with no exact integer is not a usable halting-time result.
    if status == "HALT" and not steps_exact:
        status = "HALT_NO_STEPS"

    tail = "\n".join(out.splitlines()[-8:])
    return {
        "idx": idx,
        "spec": spec,
        "status": status,
        "steps_exact": steps_exact,
        "steps_digits": len(steps_exact) if steps_exact else None,
        "nonzeros_exact": nonzeros_exact,
        "elapsed": round(elapsed, 3),
        "timed_out": timed_out,
        "rc": rc,
        "config": "strong-v1",
        "tail": tail,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    ap.add_argument("--quicksim", type=Path, default=QUICKSIM)
    ap.add_argument("--out", type=Path, default=ROOT / "bbwork" / "vendor" / "haulters_quicksim" / "attempts.jsonl")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--workers", type=int, default=48)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--start", type=int, default=0, help="0-based input offset")
    ap.add_argument("--fresh", action="store_true")
    ap.add_argument("--progress", type=int, default=40)
    args = ap.parse_args()

    specs = load_specs(args.input)
    if args.start:
        specs = specs[args.start :]
    if args.limit:
        specs = specs[: args.limit]
    if not specs:
        print("no input specs", file=sys.stderr)
        return 2

    args.out.parent.mkdir(parents=True, exist_ok=True)
    done: set[int] = set()
    if args.out.exists() and not args.fresh:
        for line in args.out.read_text(encoding="utf-8").splitlines():
            try:
                done.add(int(json.loads(line)["idx"]))
            except Exception:
                pass
        # Ignore rows from a different offset entirely; idx is absolute.
    jobs = [(args.start + i + 1, spec) for i, spec in enumerate(specs) if (args.start + i + 1) not in done]
    print(
        f"input={args.input} total={len(specs)} pending={len(jobs)} "
        f"workers={args.workers} timeout={args.timeout}s "
        f"out={args.out}",
        flush=True,
    )
    if not jobs:
        print("all requested rows already present", flush=True)
        return 0

    counts: dict[str, int] = {}
    started = time.time()
    with args.out.open("a", encoding="utf-8") as f, ThreadPoolExecutor(max_workers=args.workers) as ex:
        futures = {ex.submit(run_one, idx, spec, args): idx for idx, spec in jobs}
        for i, fut in enumerate(as_completed(futures), 1):
            row = fut.result()
            f.write(json.dumps(row) + "\n")
            f.flush()
            counts[row["status"]] = counts.get(row["status"], 0) + 1
            if row["status"] in ("HALT", "HALT_NO_STEPS", "INF") or i % args.progress == 0:
                print(
                    f"[{i}/{len(jobs)}] line={row['idx']} {row['status']} "
                    f"steps_digits={row['steps_digits']} elapsed={row['elapsed']}s",
                    flush=True,
                )
    elapsed = time.time() - started
    print(f"done in {elapsed:.1f}s counts={counts}", flush=True)
    print(f"results={args.out}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
