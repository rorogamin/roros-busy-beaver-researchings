#!/usr/bin/env python3
"""Parallel C++ LinRecur sweep over the formal 37."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CPP = ROOT / "vendor" / "busy-beaver" / "cpp" / "lin_recur"
MACHINES = ROOT / "Bb2x5_informalLast37.txt"
OUT = ROOT / "linrecur_cpp37"


def parse_result(out: str) -> dict:
    return {
        "success": "Lin Recurrence Detected" in out,
        "halted": "Halted" in out,
        "inconclusive": "Inconclusive" in out,
        "start_step": int(m.group(1)) if (m := re.search(r"start_step:\s*(\d+)", out)) else None,
        "period": int(m.group(1)) if (m := re.search(r"period:\s*(\d+)", out)) else None,
        "offset": int(m.group(1)) if (m := re.search(r"offset:\s*(-?\d+)", out)) else None,
        "steps_run": int(m.group(1)) if (m := re.search(r"steps_run:\s*(\d+)", out)) else None,
    }


def run_one(idx: int, log2_steps: int, timeout: int) -> dict:
    line_num = idx - 1
    log = OUT / "logs" / f"{idx:02d}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        p = subprocess.run(
            [str(CPP), str(MACHINES), str(line_num), str(log2_steps)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        out = p.stdout or ""
        log.write_text(out, encoding="utf-8")
        return {
            "index": idx, "line_num": line_num, "returncode": p.returncode,
            "timeout": False, "elapsed_s": round(time.monotonic() - started, 3),
            **parse_result(out), "log": str(log.relative_to(ROOT)),
        }
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout or ""
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        log.write_text(out, encoding="utf-8")
        return {
            "index": idx, "line_num": line_num, "returncode": None,
            "timeout": True, "elapsed_s": round(time.monotonic() - started, 3),
            **parse_result(out), "log": str(log.relative_to(ROOT)),
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log2-steps", type=int, default=30)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()

    machines = [x.strip() for x in MACHINES.read_text(encoding="utf-8").splitlines() if x.strip()]
    OUT.mkdir(parents=True, exist_ok=True)
    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {
            pool.submit(run_one, i, args.log2_steps, args.timeout): machine
            for i, machine in enumerate(machines, 1)
        }
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            results.append(result)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result) + "\n")
            if result.get("success") or result.get("halted"):
                print(f"DECISION index={result['index']} {result}", flush=True)
            if i % 5 == 0 or i == len(machines):
                print(f"progress {i}/{len(machines)}", flush=True)

    print(json.dumps({
        "runs": len(results),
        "successes": sum(bool(r.get("success")) for r in results),
        "halts": sum(bool(r.get("halted")) for r in results),
        "timeouts": sum(bool(r.get("timeout")) for r in results),
        "returncode_nonzero": sum(r.get("returncode") not in (0, None) for r in results),
        "log2_steps": args.log2_steps,
        "summary": str(summary.relative_to(ROOT)),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
