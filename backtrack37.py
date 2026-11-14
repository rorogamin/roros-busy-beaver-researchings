#!/usr/bin/env python3
"""Parallel backtracking proof sweep over the formal BB(2,5) 37."""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MACHINES = ROOT / "Bb2x5_informalLast37.txt"
OUT = ROOT / "backtrack37"


def run_one(idx: int, machine: str, steps: int, width: int, timeout: int) -> dict:
    started = time.monotonic()
    try:
        p = subprocess.run(
            ["py", "-3.14", str(ROOT / "backtrack_one.py"), machine, str(steps), str(width)],
            cwd=ROOT / "vendor" / "busy-beaver" / "Code",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
        out = (p.stdout or "").strip()
        try:
            result = json.loads(out.splitlines()[-1]) if out else {}
        except json.JSONDecodeError:
            result = {}
        result.update({
            "index": idx,
            "returncode": p.returncode,
            "timeout": False,
            "elapsed_s": round(time.monotonic() - started, 3),
            "stderr": (p.stderr or "")[-1000:],
        })
        return result
    except subprocess.TimeoutExpired as exc:
        return {
            "machine": machine,
            "index": idx,
            "success": False,
            "halted": False,
            "timeout": True,
            "returncode": None,
            "elapsed_s": round(time.monotonic() - started, 3),
            "stderr": "timeout",
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--width", type=int, default=2_000_000)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()

    machines = [x.strip() for x in MACHINES.read_text(encoding="utf-8").splitlines() if x.strip()]
    OUT.mkdir(parents=True, exist_ok=True)
    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {
            pool.submit(run_one, i, machine, args.steps, args.width, args.timeout): machine
            for i, machine in enumerate(machines, 1)
        }
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            results.append(result)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result) + "\n")
            if result.get("success"):
                print(f"SUCCESS index={result['index']} {result['machine']}", flush=True)
            if i % 5 == 0 or i == len(machines):
                print(f"progress {i}/{len(machines)}", flush=True)

    print(json.dumps({
        "runs": len(results),
        "successes": sum(bool(r.get("success")) for r in results),
        "timeouts": sum(bool(r.get("timeout")) for r in results),
        "returncode_nonzero": sum(r.get("returncode") not in (0, None) for r in results),
        "steps": args.steps,
        "width": args.width,
        "summary": str(summary.relative_to(ROOT)),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
