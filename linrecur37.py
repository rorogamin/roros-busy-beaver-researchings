#!/usr/bin/env python3
"""Parallel linear-recurrence (translated-cycler) sweep over the formal 37."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CODE = ROOT / "vendor" / "busy-beaver" / "Code"
MACHINES = ROOT / "Bb2x5_informalLast37.txt"
OUT = ROOT / "linrecur37"


def parse_result(out: str) -> dict:
    success = bool(re.search(r"^\s*success:\s*true\s*$", out, re.MULTILINE))
    fields = {}
    for name in ("start_step", "period", "offset"):
        m = re.search(rf"^\s*{name}:\s*(-?\d+)\s*$", out, re.MULTILINE)
        if m:
            fields[name] = int(m.group(1))
    return {"success": success, **fields}


def run_one(idx: int, machine: str, max_steps: int, timeout: int) -> dict:
    log = OUT / "logs" / f"{idx:02d}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        p = subprocess.run(
            ["py", "-3.14", "Lin_Recur_Detect.py", machine,
             "--max-steps", str(max_steps), "--no-min-start-step"],
            cwd=CODE, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=timeout,
        )
        out = p.stdout or ""
        log.write_text(out, encoding="utf-8")
        return {
            "index": idx, "machine": machine, "returncode": p.returncode,
            "timeout": False, "elapsed_s": round(time.monotonic() - started, 3),
            **parse_result(out), "log": str(log.relative_to(ROOT)),
        }
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout or ""
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        log.write_text(out, encoding="utf-8")
        return {
            "index": idx, "machine": machine, "returncode": None,
            "timeout": True, "elapsed_s": round(time.monotonic() - started, 3),
            **parse_result(out), "log": str(log.relative_to(ROOT)),
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-steps", type=int, default=10_000_000)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()

    machines = [x.strip() for x in MACHINES.read_text(encoding="utf-8").splitlines() if x.strip()]
    OUT.mkdir(parents=True, exist_ok=True)
    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {
            pool.submit(run_one, i, machine, args.max_steps, args.timeout): machine
            for i, machine in enumerate(machines, 1)
        }
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            results.append(result)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result) + "\n")
            if result.get("success"):
                print(f"SUCCESS index={result['index']} {result['machine']} {result}", flush=True)
            if i % 5 == 0 or i == len(machines):
                print(f"progress {i}/{len(machines)}", flush=True)

    print(json.dumps({
        "runs": len(results),
        "successes": sum(bool(r.get("success")) for r in results),
        "timeouts": sum(bool(r.get("timeout")) for r in results),
        "returncode_nonzero": sum(r.get("returncode") not in (0, None) for r in results),
        "max_steps": args.max_steps,
        "summary": str(summary.relative_to(ROOT)),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
