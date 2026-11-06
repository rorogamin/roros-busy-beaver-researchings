"""Parallel deep screen for standard-format holdout machines.

The existing screen37/screen608 files are ad-hoc partitions.  This driver
keeps the full list, partitions it into contiguous chunks, runs sim.exe on
all chunks, and refuses to report success unless exactly one CSV row per
machine comes back.

Usage:
    py -3.14 deep_screen.py --list bb6_specs.txt --cap 1000000000 --jobs 16
    py -3.14 deep_screen.py --list Bb2x5_informalLast37.txt --cap 10000000000

Outputs, under --out (default deep_<list-stem>_<cap>):
    partNN.txt       input chunks
    partNN.out       raw simulator output
    results.csv      idx,spec,steps,halted,score,head_min,head_max
    summary.txt      aggregate statistics and any halts
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
SIM = ROOT / "sim.exe"


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


def run_part(job: tuple[int, pathlib.Path, pathlib.Path, int]) -> tuple[int, str, str]:
    part_no, part_path, out_path, cap = job
    cmd = [str(SIM), "-c", str(cap), "-f", str(part_path)]
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    out_path.write_text(proc.stdout, encoding="utf-8")
    return part_no, proc.stdout, proc.stderr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True, type=pathlib.Path)
    ap.add_argument("--cap", required=True, type=int)
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--out", type=pathlib.Path)
    ap.add_argument("--strip-id", action="store_true",
                    help="keep only the last whitespace token on each line")
    args = ap.parse_args()

    specs = load_specs(args.list, args.strip_id)
    if not specs:
        print(f"no machine specs in {args.list}", file=sys.stderr)
        return 2
    if not SIM.exists():
        print(f"missing simulator: {SIM}", file=sys.stderr)
        return 2

    outdir = args.out or ROOT / f"deep_{args.list.stem}_{args.cap}"
    outdir.mkdir(parents=True, exist_ok=True)
    jobs = max(1, min(args.jobs, len(specs)))
    # Strided chunks: global index = part_no + local * jobs.
    chunks = [specs[i::jobs] for i in range(jobs)]
    jobspecs = []
    for i, chunk in enumerate(chunks):
        part = outdir / f"part{i:02d}.txt"
        part.write_text("".join(s + "\n" for s in chunk), encoding="utf-8")
        jobspecs.append((i, part, outdir / f"part{i:02d}.out", args.cap))

    started = time.perf_counter()
    raw: dict[int, str] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = [ex.submit(run_part, j) for j in jobspecs]
        for fut in concurrent.futures.as_completed(futures):
            part_no, stdout, stderr = fut.result()
            if stderr.strip():
                print(f"part {part_no} stderr: {stderr.strip()[:500]}", file=sys.stderr)
            raw[part_no] = stdout
    elapsed = time.perf_counter() - started

    rows = []
    for part_no, chunk in enumerate(chunks):
        lines = [ln for ln in raw.get(part_no, "").splitlines() if ln.strip()]
        if len(lines) != len(chunk):
            print(f"part {part_no}: {len(lines)} output rows for {len(chunk)} machines",
                  file=sys.stderr)
            return 2
        for local, line in enumerate(lines):
            fields = line.split(",")
            if len(fields) != 6:
                print(f"part {part_no} row {local}: bad CSV {line!r}", file=sys.stderr)
                return 2
            global_idx = part_no + local * jobs
            _, steps, halted, score, hmin, hmax = fields
            rows.append((global_idx, chunk[local], int(steps), int(halted),
                         int(score), int(hmin), int(hmax)))
    rows.sort()

    results = outdir / "results.csv"
    with results.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["idx", "spec", "steps", "halted", "score", "head_min", "head_max"])
        w.writerows(rows)

    halted = [r for r in rows if r[3]]
    top = sorted(rows, key=lambda r: (-r[4], -r[6], r[0]))[:10]
    summary = [
        f"list={args.list}",
        f"cap={args.cap:,}",
        f"machines={len(rows)}",
        f"jobs={jobs}",
        f"elapsed_seconds={elapsed:.3f}",
        f"halted={len(halted)}",
        f"max_score={max(r[4] for r in rows):,}",
        f"mean_score={sum(r[4] for r in rows) / len(rows):.2f}",
        f"min_head={min(r[5] for r in rows):,}",
        f"max_head={max(r[6] for r in rows):,}",
        "",
        "top scores:",
    ]
    for r in top:
        summary.append(f"  score={r[4]:,} idx={r[0]} span=({r[5]:,},{r[6]:,}) {r[1]}")
    if halted:
        summary.append("")
        summary.append("HALTS:")
        for r in halted:
            summary.append(f"  steps={r[2]:,} score={r[4]:,} idx={r[0]} {r[1]}")
    text = "\n".join(summary) + "\n"
    (outdir / "summary.txt").write_text(text, encoding="utf-8")
    print(text, end="")
    print(f"wrote {results}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
