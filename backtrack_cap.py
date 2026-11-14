#!/usr/bin/env python3
"""Retry only the backtracking cap hits at a larger width."""

from __future__ import annotations

import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "backtrack_cap"
TARGETS = {
    3: "1RB2RA3LA4LA2RB_2LA3RA---0RA1LA",
    33: "1RB2RB4LA2RA1LA_2LA4RA3LA---3RA",
    14: "1RB2LA0RB4LB1RA_1LA3RA1RA---0LA",
}


def run_one(index: int, machine: str, width: int, timeout: int) -> dict:
    started = time.monotonic()
    try:
        p = subprocess.run(
            ["py", "-3.14", str(ROOT / "backtrack_one.py"), machine, "200", str(width)],
            cwd=ROOT / "vendor" / "busy-beaver" / "Code",
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout,
        )
        out = (p.stdout or "").strip()
        try:
            result = json.loads(out.splitlines()[-1]) if out else {}
        except json.JSONDecodeError:
            result = {}
        result.update({
            "index": index, "returncode": p.returncode, "timeout": False,
            "elapsed_s": round(time.monotonic() - started, 3),
            "stderr": (p.stderr or "")[-500:],
        })
        return result
    except subprocess.TimeoutExpired:
        return {
            "index": index, "machine": machine, "success": False,
            "halted": False, "timeout": True, "returncode": None,
            "elapsed_s": round(time.monotonic() - started, 3),
            "stderr": "timeout",
        }


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    with ThreadPoolExecutor(max_workers=3) as pool:
        futures = [pool.submit(run_one, i, m, 2_000_000, 120) for i, m in TARGETS.items()]
        for fut in as_completed(futures):
            result = fut.result()
            print(json.dumps(result, sort_keys=True), flush=True)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
