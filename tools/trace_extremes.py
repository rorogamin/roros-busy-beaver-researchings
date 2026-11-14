#!/usr/bin/env python3
"""Trace a 2-symbol/5-symbol (or general) TM at tape extremes.

Runs the machine from the blank tape and logs the configuration every time the
head visits a new leftmost or rightmost cell while in a chosen state (default A).
This is the natural macro decomposition for two-state machines: an "extreme
return" is the point where a counter parameter has advanced by one.

Usage: python tools/trace_extremes.py "<spec>" [steps] [state]
"""
import sys


def parse(spec):
    """spec like 1RB---4LB1RA4RA_2LB2LA3RA4LB0RB -> rows[state][sym] = (write,move,next)."""
    rows = spec.split('_')
    table = {}
    for st, row in enumerate(rows):
        i = 0
        sym = 0
        while i < len(row):
            if row[i:i + 3] == '---':
                i += 3
                sym += 1
                continue
            if i + 3 > len(row):
                break
            chunk = row[i:i + 3]
            if len(chunk) == 3 and chunk[0] in '0123456789' and chunk[1] in 'RL' and chunk[2].isalpha():
                table[(st, sym)] = (int(chunk[0]), 1 if chunk[1] == 'R' else -1, ord(chunk[2]) - 65)
                i += 3
                sym += 1
            elif row[i] == '-' :
                i += 1
            else:
                raise ValueError(f"bad row {row!r} at {i}")
    return table


def rle(tape, lo, hi, head):
    out = []
    for p in range(lo, hi + 1):
        s = tape.get(p, 0)
        out.append(('[' + str(s) + ']') if p == head else str(s))
    return ''.join(out)


def main():
    spec = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5_000_000
    watch = ord(sys.argv[3]) - 65 if len(sys.argv) > 3 else 0
    t = parse(spec)
    tape = {}
    head, st = 0, 0
    lmin = rmax = 0
    events = 0
    for step in range(1, limit + 1):
        key = (st, tape.get(head, 0))
        if key not in t:
            print(f"HALT/undefined state={chr(65+st)} sym={tape.get(head,0)} at step {step} head={head}")
            print("tape:", rle(tape, lmin, rmax, head))
            return
        w, mv, ns = t[key]
        tape[head] = w
        head += mv
        st = ns
        new = head < lmin or head > rmax
        if new:
            lmin = min(lmin, head)
            rmax = max(rmax, head)
        if st == watch and (new or step < 200):
            events += 1
            if events <= 60 or events % 20 == 0:
                lo = max(lmin, head - 12)
                hi = min(rmax, head + 12)
                print(f"step={step:>12} A@{head:>7} span=[{lmin},{rmax}] len={rmax-lmin+1} tape={rle(tape, lo, hi, head)}")
    print(f"no halt in {limit} steps; head={head} state={chr(65+st)} span=[{lmin},{rmax}]")
    print("tape:", rle(tape, max(lmin, head - 20), min(rmax, head + 20), head))


if __name__ == '__main__':
    main()
