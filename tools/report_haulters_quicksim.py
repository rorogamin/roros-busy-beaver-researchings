#!/usr/bin/env python3
"""Summarise QuickSim attempts for haulters_pseudoholdouts_31415.txt."""
from __future__ import annotations

import argparse
import datetime as dt
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] if len(HERE.parents) > 1 else HERE
DEFAULT_INPUT = Path(r"C:\Users\Rowan\Downloads\haulters_pseudoholdouts_31415.txt")
DEFAULT_ATTEMPTS = ROOT / "bbwork" / "vendor" / "haulters_quicksim" / "attempts.jsonl"


def load_specs(path: Path) -> list[str]:
    return [x.strip() for x in path.read_text(encoding="utf-8-sig").splitlines() if x.strip()]


def step_key(row: dict):
    s = row.get("steps_exact")
    if not s:
        return (10**9, "")
    # Compare huge integers by digit count first, then lexicographically.
    return (len(s), s)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    ap.add_argument("--attempts", type=Path, default=DEFAULT_ATTEMPTS)
    ap.add_argument("--outdir", type=Path, default=DEFAULT_ATTEMPTS.parent)
    args = ap.parse_args()

    specs = load_specs(args.input)
    rows: dict[int, dict] = {}
    duplicates = 0
    bad = 0
    if args.attempts.exists():
        for line in args.attempts.read_text(encoding="utf-8").splitlines():
            try:
                row = json.loads(line)
                idx = int(row["idx"])
            except Exception:
                bad += 1
                continue
            if idx in rows:
                duplicates += 1
            rows[idx] = row
    args.outdir.mkdir(parents=True, exist_ok=True)

    counts = Counter(r["status"] for r in rows.values())
    halts = sorted((r for r in rows.values() if r["status"] == "HALT" and r.get("steps_exact")), key=step_key)
    unresolved = sorted((r for r in rows.values() if r["status"] != "HALT" or not r.get("steps_exact")), key=lambda r: r["idx"])
    missing = [i for i in range(1, len(specs) + 1) if i not in rows]

    tsv = args.outdir / "halting_times.tsv"
    with tsv.open("w", encoding="utf-8", newline="") as f:
        f.write("rank\tline\tsteps_exact\tsteps_digits\telapsed_s\tspec\n")
        for rank, row in enumerate(halts, 1):
            f.write(
                f"{rank}\t{row['idx']}\t{row['steps_exact']}\t{row.get('steps_digits')}\t"
                f"{row.get('elapsed')}\t{row['spec']}\n"
            )

    unresolved_tsv = args.outdir / "unresolved.tsv"
    with unresolved_tsv.open("w", encoding="utf-8", newline="") as f:
        f.write("line\tstatus\telapsed_s\tspec\n")
        for row in unresolved:
            f.write(f"{row['idx']}\t{row['status']}\t{row.get('elapsed')}\t{row['spec']}\n")

    summary = args.outdir / "summary.md"
    lines = [
        "# haulters_pseudoholdouts_31415 QuickSim report",
        "",
        f"- Generated: `{dt.datetime.now().astimezone().isoformat(timespec='seconds')}`",
        f"- Input: `{args.input}`",
        f"- Input machines: **{len(specs)}**",
        f"- Result rows: **{len(rows)}**",
        f"- Missing rows: **{len(missing)}**",
        f"- Duplicate rows ignored: **{duplicates}**",
        f"- Unparseable rows: **{bad}**",
        "",
        "## Status counts",
        "",
        "| Status | Count |",
        "|---|---:|",
    ]
    for status, count in sorted(counts.items()):
        lines.append(f"| {status} | {count} |")
    lines += [
        "",
        "`TIMEOUT` and `LOOP_LIMIT` are **not** non-halting proofs; they are unresolved runs.",
        "",
        "## Halted machines",
        "",
        f"- Halts with an exact step count: **{len(halts)}**",
    ]
    if halts:
        lines += [
            f"- Smallest: line {halts[0]['idx']}, {halts[0]['steps_exact']} steps",
            f"- Largest: line {halts[-1]['idx']}, {halts[-1]['steps_exact']} steps",
            "",
            "| Rank | Line | Steps | Digits |",
            "|---:|---:|---:|---:|",
        ]
        for rank, row in enumerate(halts[:20], 1):
            steps = row["steps_exact"]
            shown = steps if len(steps) <= 80 else steps[:40] + "…" + steps[-20:]
            lines.append(f"| {rank} | {row['idx']} | `{shown}` | {row['steps_digits']} |")
    if missing:
        lines += ["", f"Missing line numbers (first 20): `{missing[:20]}`"]
    lines += [
        "",
        "## Files",
        "",
        f"- `{tsv.name}` — all resolved halts sorted by exact step count",
        f"- `{unresolved_tsv.name}` — unresolved/other rows",
        f"- `{args.attempts.name}` — raw append-only attempts",
        "",
    ]
    summary.write_text("\n".join(lines), encoding="utf-8")
    print(f"rows={len(rows)} halts={len(halts)} missing={len(missing)} counts={dict(counts)}")
    print(f"wrote {summary} {tsv} {unresolved_tsv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
