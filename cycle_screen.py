"""Parallel translated-cycle screen for standard-format holdout machines.

The existing cycle screen checked 37 machines at 10^9 with 10^6 checkpoints.
This driver runs each machine independently through cyc.exe, writes one log
per machine, and refuses to report success unless every machine produced
exactly one recognised status line.

A CYCLE result is a finite translated-cycle witness.  NO_CYCLE is only a
lower bound at the stated cap; it does not prove nonhalting.

Usage:
    py -3.14 cycle_screen.py --list bb2x5_holdouts37.txt \
        --cap 10000000000 --interval 10000000 --jobs 8

Outputs, under --out (default cycle_<list-stem>_<cap>_<interval>):
    logs/NNN.out     raw cyc.exe output
    logs/NNN.err     stderr, if any
    results.csv      idx,spec,status,detail,elapsed_seconds
    summary.txt      aggregate result and every CYCLE/HALT witness
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent
CYC = ROOT / "cyc.exe"


def load_specs(path: pathlib.Path, strip_id: bool) -> list[str]:
    specs: list[str] = []
    with path.open(encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            if strip_id and " " in line:
                line = line.split()[-1]
            if "_" not in line or " " in line:
                continue
            specs.append(line)
    return specs


def run_one(job: tuple[int, str, int, int, pathlib.Path]) -> tuple[int, str, int, str, str, float]:
    idx, spec, cap, interval, logs = job
    started = time.perf_counter()
    proc = subprocess.run(
        [str(CYC), str(cap), str(interval), spec],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    elapsed = time.perf_counter() - started
    (logs / f"{idx:03d}.out").write_text(proc.stdout, encoding="utf-8")
    if proc.stderr:
        (logs / f"{idx:03d}.err").write_text(proc.stderr, encoding="utf-8")
    return idx, spec, proc.returncode, proc.stdout, proc.stderr, elapsed


def classify(stdout: str) -> tuple[str, str]:
    lines = [ln.strip() for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        return "ERROR", "no output"
    first = lines[0]
    if first.startswith("CYCLE "):
        return "CYCLE", first
    if first.startswith("HALT "):
        return "HALT", first
    if first.startswith("NO_CYCLE "):
        return "NO_CYCLE", first
    return "ERROR", first[:200]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True, type=pathlib.Path)
    ap.add_argument("--cap", required=True, type=int)
    ap.add_argument("--interval", required=True, type=int)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--out", type=pathlib.Path)
    ap.add_argument("--strip-id", action="store_true")
    ap.add_argument("--resume", action="store_true",
                    help="reuse nonempty logs from a prior interrupted run")
    args = ap.parse_args()

    specs = load_specs(args.list, args.strip_id)
    if not specs:
        print(f"no machine specs in {args.list}", file=sys.stderr)
        return 2
    if not CYC.exists():
        print(f"missing cycle detector: {CYC}", file=sys.stderr)
        return 2
    if args.interval <= 0:
        print("--interval must be positive", file=sys.stderr)
        return 2

    outdir = args.out or ROOT / f"cycle_{args.list.stem}_{args.cap}_{args.interval}"
    logs = outdir / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    jobs = max(1, min(args.jobs, len(specs)))
    started = time.perf_counter()

    rows = []
    pending = []
    for idx, spec in enumerate(specs):
        log = logs / f"{idx:03d}.out"
        if args.resume and log.exists() and log.stat().st_size:
            status, detail = classify(log.read_text(encoding="utf-8", errors="replace"))
            if status != "ERROR":
                rows.append((idx, spec, status, detail, 0.0))
                continue
        pending.append((idx, spec))

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = [
            ex.submit(run_one, (idx, spec, args.cap, args.interval, logs))
            for idx, spec in pending
        ]
        for fut in concurrent.futures.as_completed(futures):
            idx, spec, rc, stdout, stderr, elapsed = fut.result()
            status, detail = classify(stdout)
            if rc != 0 and status != "ERROR":
                status, detail = "ERROR", f"exit {rc}: {detail}"
            rows.append((idx, spec, status, detail, elapsed))
    rows.sort()
    elapsed = time.perf_counter() - started

    results = outdir / "results.csv"
    with results.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["idx", "spec", "status", "detail", "elapsed_seconds"])
        for idx, spec, status, detail, secs in rows:
            w.writerow([idx, spec, status, detail, f"{secs:.3f}"])

    counts = {k: 0 for k in ("NO_CYCLE", "CYCLE", "HALT", "ERROR")}
    for row in rows:
        counts[row[2]] = counts.get(row[2], 0) + 1

    summary = [
        f"list={args.list}",
        f"cap={args.cap:,}",
        f"interval={args.interval:,}",
        f"machines={len(rows)}",
        f"jobs={jobs}",
        f"elapsed_seconds={elapsed:.3f}",
        f"no_cycle={counts['NO_CYCLE']}",
        f"cycles={counts['CYCLE']}",
        f"halts={counts['HALT']}",
        f"errors={counts['ERROR']}",
    ]
    interesting = [r for r in rows if r[2] in ("CYCLE", "HALT", "ERROR")]
    if interesting:
        summary.append("")
        summary.append("NON-NO_CYCLE ROWS:")
        for idx, spec, status, detail, secs in interesting:
            summary.append(f"  idx={idx} status={status} {detail}")
            summary.append(f"    {spec}")
    text = "\n".join(summary) + "\n"
    (outdir / "summary.txt").write_text(text, encoding="utf-8")
    print(text, end="")
    print(f"wrote {results}")
    return 0 if counts["ERROR"] == 0 and counts["HALT"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
