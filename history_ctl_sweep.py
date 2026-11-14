#!/usr/bin/env python3
"""Bounded CPS-history and CTL sweep over the formal BB(2,5) 37.

This is a search for a certificate, not a proof by itself.  CPS success emits
@savask's certificate format into the per-run log; every claimed success is
kept for independent checking.  CTL success is recorded as a decider result,
not treated as a formal proof.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CODE = ROOT / "vendor" / "busy-beaver" / "Code"
MACHINES = ROOT / "Bb2x5_informalLast37.txt"
OUT = ROOT / "history_ctl"


def machine_list() -> list[str]:
    return [line.strip() for line in MACHINES.read_text(encoding="utf-8").splitlines() if line.strip()]


def run_one(tag: str, argv: list[str], timeout: int) -> dict:
    log = OUT / "logs" / f"{tag}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    full = ["py", "-3.14", *argv]
    started = __import__("time").monotonic()
    try:
        p = subprocess.run(
            full,
            cwd=CODE,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        out = p.stdout or ""
        log.write_text(out, encoding="utf-8")
        elapsed = round(__import__("time").monotonic() - started, 3)
        return {
            "tag": tag,
            "argv": argv,
            "returncode": p.returncode,
            "timeout": False,
            "elapsed_s": elapsed,
            "cps_success": "Proven Infinite" in out or '"success": true' in out,
            "ctl_success": "Success :)" in out,
            "log": str(log.relative_to(ROOT)),
        }
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        log.write_text(out, encoding="utf-8")
        elapsed = round(__import__("time").monotonic() - started, 3)
        return {
            "tag": tag,
            "argv": argv,
            "returncode": None,
            "timeout": True,
            "elapsed_s": elapsed,
            "cps_success": "Proven Infinite" in out or '"success": true' in out,
            "ctl_success": "Success :)" in out,
            "log": str(log.relative_to(ROOT)),
        }


def jobs_for(machine: str, idx: int) -> list[tuple[str, list[str], int]]:
    jobs = [
        (
            f"cps_lru_{idx:02d}",
            ["CPS.py", machine, "--lru-history", "--max-block-size", "10",
             "--max-steps", "1000000", "--max-iters", "1000",
             "--max-configs", "50000", "--max-edges", "50000", "--savask-cert"],
            120,
        ),
        (
            f"cps_fixed2_{idx:02d}",
            ["CPS.py", machine, "--fixed-history", "2", "--max-block-size", "10",
             "--max-steps", "1000000", "--max-iters", "1000",
             "--max-configs", "50000", "--max-edges", "50000", "--savask-cert"],
            120,
        ),
        (
            f"cps_fixed3_{idx:02d}",
            ["CPS.py", machine, "--fixed-history", "3", "--max-block-size", "10",
             "--max-steps", "1000000", "--max-iters", "1000",
             "--max-configs", "50000", "--max-edges", "50000", "--savask-cert"],
            120,
        ),
    ]
    # CTL families are cheap enough to run at a few block scales.  The same
    # cutoff is used for each family so the result is comparable.
    for ctl in (1, 2, 3, 4):
        for block in (1, 2, 3):
            jobs.append(
                (
                    f"ctl{ctl}_b{block}_{idx:02d}",
                    [f"CTL{ctl}.py", machine, "1000000", str(block), "0"],
                    45,
                )
            )
    return jobs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--limit", type=int, default=0, help="only first N machines (debug)")
    args = parser.parse_args()

    machines = machine_list()
    if args.limit:
        machines = machines[: args.limit]

    OUT.mkdir(parents=True, exist_ok=True)
    all_jobs = []
    for idx, machine in enumerate(machines, 1):
        all_jobs.extend(jobs_for(machine, idx))

    summary = OUT / "summary.jsonl"
    summary.write_text("", encoding="utf-8")
    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {
            pool.submit(run_one, tag, argv, timeout): (tag, argv, timeout)
            for tag, argv, timeout in all_jobs
        }
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            results.append(result)
            with summary.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(result) + "\n")
            if result["cps_success"] or result["ctl_success"]:
                print(f"CERTIFICATE-RESULT {result['tag']}: {result['log']}", flush=True)
            if i % 25 == 0 or i == len(all_jobs):
                print(f"progress {i}/{len(all_jobs)}", flush=True)

    cps = sum(1 for r in results if r["cps_success"])
    ctl = sum(1 for r in results if r["ctl_success"])
    timeouts = sum(1 for r in results if r["timeout"])
    print(json.dumps({
        "runs": len(results),
        "cps_successes": cps,
        "ctl_successes": ctl,
        "timeouts": timeouts,
        "machines": len(machines),
        "summary": str(summary.relative_to(ROOT)),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
