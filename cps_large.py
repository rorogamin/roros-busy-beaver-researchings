#!/usr/bin/env python3
"""Larger-block CPS/CTL probe for the two structured BB(2,5) holdouts.

This deliberately goes beyond the earlier block<=10 / CTL block<=3 sweep.
It is a bounded search, not a proof.  Any CPS certificate is saved in the
per-run log and listed in summary.jsonl for independent checking.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CODE = ROOT / "vendor" / "busy-beaver" / "Code"
OUT = ROOT / "cps_large"

MACHINES = [
    ("05", "1RB---3RA2LA2RB_2LB3LA4LB4RA0RA"),
    ("14", "1RB2LA0RB4LB1RA_1LA3RA1RA---0LA"),
]


def jobs_for(tag: str, machine: str) -> list[tuple[str, list[str], int]]:
    jobs: list[tuple[str, list[str], int]] = []
    # CPS: block sizes beyond the earlier 1..10 pass, with the standard
    # 3*block window.  Test both plain and LRU-history CPS.
    for block in range(11, 21):
        for mode, extra in (("plain", []), ("lru", ["--lru-history"])):
            jobs.append(
                (
                    f"cps_{mode}_b{block}_{tag}",
                    [
                        "CPS.py", machine, *extra,
                        "--block-size", str(block),
                        "--window-size", str(3 * block),
                        "--max-steps", "5000000",
                        "--max-iters", "1000",
                        "--max-configs", "100000",
                        "--max-edges", "100000",
                        "--savask-cert",
                    ],
                    180,
                )
            )
    # CTL: block sizes beyond the earlier 1..3 pass.
    for ctl in (1, 2, 3, 4):
        for block in range(4, 11):
            jobs.append(
                (
                    f"ctl{ctl}_b{block}_{tag}",
                    [f"CTL{ctl}.py", machine, "1000000", str(block), "0"],
                    60,
                )
            )
    return jobs


def run_one(tag: str, argv: list[str], timeout: int) -> dict:
    log = OUT / "logs" / f"{tag}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        p = subprocess.run(
            ["py", "-3.14", *argv],
            cwd=CODE,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        out = p.stdout or ""
        log.write_text(out, encoding="utf-8")
        return {
            "tag": tag,
            "argv": argv,
            "returncode": p.returncode,
            "timeout": False,
            "elapsed_s": round(time.monotonic() - started, 3),
            "cps_success": "Proven Infinite" in out,
            "ctl_success": "Success :)" in out,
            "certificate": "Result " in out and "--savask-cert" in argv,
            "log": str(log.relative_to(ROOT)),
        }
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout or ""
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        log.write_text(out, encoding="utf-8")
        return {
            "tag": tag,
            "argv": argv,
            "returncode": None,
            "timeout": True,
            "elapsed_s": round(time.monotonic() - started, 3),
            "cps_success": "Proven Infinite" in out,
            "ctl_success": "Success :)" in out,
            "certificate": "Result " in out and "--savask-cert" in argv,
            "log": str(log.relative_to(ROOT)),
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    all_jobs = []
    for tag, machine in MACHINES:
        all_jobs.extend(jobs_for(tag, machine))

    if args.dry_run:
        print(json.dumps([{"tag": t, "argv": a, "timeout": to} for t, a, to in all_jobs], indent=2))
        return 0

    OUT.mkdir(parents=True, exist_ok=True)
    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {pool.submit(run_one, t, a, to): t for t, a, to in all_jobs}
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            results.append(result)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result) + "\n")
            if result["cps_success"] or result["ctl_success"]:
                print(f"RESULT {result['tag']}: {result['log']}", flush=True)
            if i % 10 == 0 or i == len(all_jobs):
                print(f"progress {i}/{len(all_jobs)}", flush=True)

    print(json.dumps({
        "runs": len(results),
        "cps_successes": sum(bool(r["cps_success"]) for r in results),
        "ctl_successes": sum(bool(r["ctl_success"]) for r in results),
        "timeouts": sum(bool(r["timeout"]) for r in results),
        "returncode_nonzero": sum(r["returncode"] not in (0, None) for r in results),
        "summary": str(summary.relative_to(ROOT)),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
