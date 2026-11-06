"""Machine factory: sample random machines in a domain, run them with the fast
C simulator, and keep the longest halting runs plus notable non-halting
runners.

Usage:
    py -3.14 factory.py --n 2 --m 5 --samples 20000 --cap 1000000 --jobs 8

The output is a TSV summary in specimens/ plus one file per top specimen.
Machines are random over the standard format, so no claim of exhaustiveness
is made -- this is a specimen hunt, not an enumeration.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import random
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
SIM = ROOT / "sim.exe"


def rand_machine(rng, n, m, halt_prob):
    blocks = []
    for _s in range(n):
        toks = []
        for _v in range(m):
            if rng.random() < halt_prob:
                toks.append("---")
            else:
                w = rng.randrange(m)
                d = rng.choice("LR")
                nx = chr(ord("A") + rng.randrange(n))
                toks.append(f"{w}{d}{nx}")
        blocks.append("".join(toks))
    return "_".join(blocks)


def run_batch(specs, cap, path):
    path.write_text("".join(s + "\n" for s in specs))
    out = subprocess.run([str(SIM), "-c", str(cap), "-f", str(path)],
                         capture_output=True, text=True)
    rows = []
    for line in out.stdout.splitlines():
        parts = line.split(",")
        if len(parts) < 6:
            continue
        rows.append((int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3])))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2)
    ap.add_argument("--m", type=int, default=5)
    ap.add_argument("--samples", type=int, default=20000)
    ap.add_argument("--cap", type=int, default=1_000_000)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--halt-prob", type=float, default=0.12)
    ap.add_argument("--seed", type=int, default=20261106)
    ap.add_argument("--out", default="specimens")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    outdir = ROOT / args.out
    outdir.mkdir(exist_ok=True)
    batch = max(1, args.samples // (args.jobs * 4))
    procs = []
    results = []
    tmpdir = pathlib.Path(tempfile.mkdtemp(prefix="bbfactory_", dir=str(ROOT)))
    done = 0

    specs = []
    idx = 0
    total = args.samples
    while done < total or procs:
        while len(procs) < args.jobs and idx < total:
            chunk = [rand_machine(rng, args.n, args.m, args.halt_prob)
                     for _ in range(min(batch, total - idx))]
            idx += len(chunk)
            path = tmpdir / f"chunk{idx}.txt"
            path.write_text("".join(s + "\n" for s in chunk))
            p = subprocess.Popen([str(SIM), "-c", str(args.cap), "-f", str(path)],
                                 stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                 text=True)
            procs.append((p, chunk))
        for p, chunk in procs[:]:
            out, _ = p.communicate()
            procs.remove((p, chunk))
            done += len(chunk)
            for line in out.splitlines():
                parts = line.split(",")
                if len(parts) < 6:
                    continue
                i, steps, halted, score = int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3])
                results.append((halted, steps, score, chunk[i]))
            if done % (batch * 4) == 0 or done >= total:
                halted = sum(1 for r in results if r[0])
                print(f"  {done}/{total} machines, {halted} halted", flush=True)

    halters = sorted((r for r in results if r[0]), key=lambda r: -r[1])
    runners = sorted((r for r in results if not r[0]), key=lambda r: -r[2])
    print(f"\n{args.n}x{args.m}: {len(results)} sampled, {len(halters)} halters, "
          f"{len(runners)} runners (cap {args.cap})")
    print("top halters:")
    for halted, steps, score, spec in halters[:10]:
        print(f"  steps={steps+1:>12} score={score:>8} {spec}")
    print("top non-halting scores:")
    for halted, steps, score, spec in runners[:5]:
        print(f"  score={score:>8} {spec}")

    stamp = f"{args.n}x{args.m}_{args.seed}"
    with open(outdir / f"factory_{stamp}.tsv", "w", encoding="utf-8") as f:
        f.write("kind\tsteps\tscore\tspec\n")
        for halted, steps, score, spec in halters[:50]:
            f.write(f"halt\t{steps+1}\t{score}\t{spec}\n")
            (outdir / f"halt_{steps+1}_{stamp}.txt").write_text(spec + "\n")
        for halted, steps, score, spec in runners[:50]:
            f.write(f"runner\t{steps}\t{score}\t{spec}\n")
            (outdir / f"runner_{score}_{stamp}.txt").write_text(spec + "\n")
    print(f"wrote {outdir}/factory_{stamp}.tsv")


if __name__ == "__main__":
    main()
