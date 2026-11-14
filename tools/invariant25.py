#!/usr/bin/env python3
"""Empirical check of the invariant used in the non-halting proof for
BB(2,5) holdout 1RB2LA1LA4RA2LA_0LA3RB3LB2RB---.

Claim (step-level inductive invariant):
  state A at position p  =>  every 4 on the tape is at a position <= p
  state B at position p  =>  every 4 on the tape is at a position <  p

Consequence: state B never sits on a 4, so the only undefined transition
(B on 4) is never taken, hence the machine never halts.

This script parses the spec, prints the table, and checks the invariant at
every step of a long run.

Usage: python invariant25.py "<spec>" [steps]
"""
import sys


def parse(spec):
    rows = spec.split('_')
    table = {}
    for st, row in enumerate(rows):
        i = sym = 0
        while i < len(row):
            if row[i:i + 3] == '---':
                i += 3
                sym += 1
                continue
            chunk = row[i:i + 3]
            if len(chunk) == 3 and chunk[0].isdigit() and chunk[1] in 'RL' and chunk[2].isalpha():
                table[(st, sym)] = (int(chunk[0]), 1 if chunk[1] == 'R' else -1, ord(chunk[2]) - 65)
                i += 3
                sym += 1
            else:
                raise ValueError(f"bad chunk {row[i:i+3]!r} in {row!r}")
    return table


def main():
    spec = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 20_000_000
    t = parse(spec)
    print("transition table (state, read) -> (write, move, next); missing = halt:")
    for (st, sym) in sorted(t):
        w, mv, ns = t[(st, sym)]
        print(f"  {chr(65+st)}{sym} -> {w}{'RL'[mv < 0]}{chr(65+ns)}")
    if len(t) != 9:
        print(f"WARNING: {len(t)} transitions parsed, expected 9 for a one-halt machine")

    tape = {}
    head = st = 0
    fours = set()
    a_checks = b_checks = 0
    for step in range(1, limit + 1):
        key = (st, tape.get(head, 0))
        if st == 0:
            a_checks += 1
            if fours and max(fours) > head:
                print(f"INVARIANT FAILED (A) step={step} head={head} max4={max(fours)}")
                return 1
        else:
            b_checks += 1
            if fours and max(fours) >= head:
                print(f"INVARIANT FAILED (B) step={step} head={head} max4={max(fours)}")
                return 1
        if key not in t:
            print(f"HALTED step={step} state={chr(65+st)} head={head} sym={tape.get(head,0)}")
            print(f"INVARIANT FAILED: reached the halting transition ({a_checks} A-checks, {b_checks} B-checks)")
            return 1
        w, mv, ns = t[key]
        old = tape.get(head, 0)
        if old == 4:
            fours.discard(head)
        tape[head] = w
        if w == 4:
            fours.add(head)
        head += mv
        st = ns
    print(f"OK: {limit} steps, invariant held at {a_checks} A-steps and {b_checks} B-steps, no halt")
    print(f"final: state={chr(65+st)} head={head} fours={sorted(fours)}"
          f" span=({min(tape)}, {max(tape)})" if tape else "")
    return 0


if __name__ == '__main__':
    sys.exit(main())
