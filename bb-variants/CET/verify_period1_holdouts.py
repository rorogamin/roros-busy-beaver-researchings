#!/usr/bin/env python3
"""Verify the one-step translated cycles found in CET(4) holdouts.

For a machine in `all_holdouts_cet4.txt`, run from the standard CET start
(A1 at 0, A2 at 2, blank tape).  A cycle is a pair of times k0 and k0+1 with

  * the same pair of states,
  * the same head distance,
  * both heads displaced by the same nonzero d,
  * equal 5-cell tapes around each head after translating by d,
  * no collision.

Then the one-step transition repeats forever in the translated frame, so the
pair is non-halting.  This is a finite local certificate, not a Rocq proof.
"""
import sys


def parse(line):
    a1, a2 = line.strip().split('|')

    def ag(s):
        rows = []
        for row in s.split('_'):
            trs = []
            for i in range(0, 6, 3):
                trs.append((int(row[i]), 1 if row[i + 1] == 'R' else -1,
                            ord(row[i + 2]) - 65))
            rows.append(trs)
        return rows
    return ag(a1), ag(a2)


def check(line, cap=5000, r=2):
    a1, a2 = parse(line)
    t, p1, p2, s1, s2 = {}, 0, 2, 0, 0
    for k in range(cap):
        key = (s1, s2, p2 - p1,
               tuple(t.get(p1 + z, 0) for z in range(-r, r + 1)),
               tuple(t.get(p2 + z, 0) for z in range(-r, r + 1)))
        if k and key == prev_key:
            d1, d2 = p1 - prev_p1, p2 - prev_p2
            if d1 == d2 and d1:
                return k - 1, d1, p1, p2
        prev_key, prev_p1, prev_p2 = key, p1, p2
        x, y = a1[s1][t.get(p1, 0)], a2[s2][t.get(p2, 0)]
        t[p1], t[p2] = x[0], y[0]
        p1 += x[1]; s1 = x[2]
        p2 += y[1]; s2 = y[2]
        if p1 == p2:
            return None
    return None


def main():
    lines = open('all_holdouts_cet4.txt').read().splitlines()
    out = []
    for i, line in enumerate(lines[:100]):
        r = check(line)
        if r:
            out.append((i, line, r))
    for i, line, r in out:
        print(i, r[0], r[1], f'p1={r[2]} p2={r[3]}', line)
    print(f'period-1 translated cycles: {len(out)}/100')
    return 0


if __name__ == '__main__':
    sys.exit(main())
