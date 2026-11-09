"""Bounded local search over 2-symbol machines.

Idea (from the census's own history): long-running machines are easier to *find*
than to design, but a fixed step cap cannot distinguish "halts late" from
"never halts" -- that is the halting problem.  So this tool only ever reports
**candidates**: machines that actually halted inside the cap, ranked by steps.

Usage:
    python tools/search.py [--trials N] [--cap N] [--mut K] [seed files...]

Mutation model: pick K rows of the table at random and replace each with a random
2-symbol transition (random write, direction, and successor state).  The state
count is fixed, so every mutant is comparable to its seed.
"""

import argparse
import random
import sys

import tm


def random_row(n, rng):
    nxt = rng.randrange(n + 1)
    return (rng.randrange(2), rng.choice('LR'), None if nxt == n else nxt)


def mutate(table, n, k, rng):
    t = dict(table)
    for _ in range(k):
        s = rng.randrange(n)
        b = rng.randrange(2)
        t[(s, b)] = random_row(n, rng)
    return tm.TM(n, t)


def search(path, trials, cap, k, rng):
    seed = tm.load(path)
    rows = []
    for _ in range(trials):
        m = mutate(seed.t, seed.n, k, rng)
        steps, tape, head, state, halted = m.run(max_steps=cap)
        if halted:
            rows.append((steps, m.score(tape), head, seed.n, m))
    rows.sort(key=lambda r: -r[0])
    return seed, rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('seeds', nargs='*', default=['machines/rung_omega_3lvl.txt'])
    ap.add_argument('--trials', type=int, default=150)
    ap.add_argument('--cap', type=int, default=120_000)
    ap.add_argument('--mut', type=int, default=1)
    ap.add_argument('--seed', type=int, default=20261101)
    args = ap.parse_args()

    rng = random.Random(args.seed)
    for path in args.seeds:
        seed, rows = search(path, args.trials, args.cap, args.mut, rng)
        base_steps, base_tape, _, _, base_halted = seed.run(max_steps=args.cap)
        print(f'== {path}  states={seed.n} rows={len(seed.t)}')
        print(f'   seed: {"halted at " + str(base_steps) if base_halted else "no halt in " + str(args.cap)}'
              f'  score={seed.score(base_tape)}')
        print(f'   {args.trials} mutants (K={args.mut}, cap={args.cap}): '
              f'{len(rows)} halted')
        for steps, score, head, n, m in rows[:8]:
            print(f'     steps={steps:>8}  score={score:>5}  head={head:>6}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
