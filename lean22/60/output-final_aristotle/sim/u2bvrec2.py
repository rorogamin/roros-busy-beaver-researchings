"""Segment the `P3` row of §48 (the carry meets a *second* `U(2,8) V(1)`) into fixed
stretches and excursions.

Configuration:

```
0 0 0 . U(2,2) V(1) u . U(2,8) V(1) . u^7 . U(2,8) V(1) . u^(sg+4) . U(1,2m+2) 0
```

Cells `0 .. 62` are the fixed prefix (it ends with the second `V(1)`); the run of `u`s
starts at cell `63`.  The script splits the computation at every moment the head crosses
from cell `62` to cell `63` and back, and prints each stretch: its length, the state and
head cell at its ends, and the cells it touches.

Exploratory only; nothing here is machine-checked.
"""

import sys
from u21b import T, U, V, u
from toklib import parse, name

CUT = 63


def word(sg, m):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + U(2, 8) + V(1) + u * 7
            + U(2, 8) + V(1) + u * (sg + 4) + U(1, 2 * m + 2) + [0])


def out(sg, m):
    return (U(2, 1) + U(4, 1) + u + u + U(2, 2) + V(1) + u * 9 + U(1, 2)
            + u * sg + U(1, 2 * m + 22) + [0])


def steps(sg, m):
    return 1363 + 60 * sg + 100 * m


def check(sgrange=range(0, 5), mrange=range(0, 5)):
    bad = 0
    for sg in sgrange:
        for m in mrange:
            l = list(word(sg, m)); q, k = 'B', 3
            for _ in range(steps(sg, m)):
                tr = T[(q, l[k])]
                if tr is None:
                    print('HALT sg=%d m=%d' % (sg, m)); bad += 1; break
                w, d, s = tr
                l[k] = w; k += d; q = s
                if not (0 <= k < len(l)):
                    print('OUT sg=%d m=%d' % (sg, m)); bad += 1; break
            else:
                if (q, k) != ('B', 0) or l != out(sg, m):
                    print('MISMATCH sg=%d m=%d -> %s%d' % (sg, m, q, k)); bad += 1
    print('mismatches:', bad)


def segment(sg, m, verbose=True):
    l = list(word(sg, m)); q, k = 'B', 3
    n = steps(sg, m)
    segs = []
    cur = [q, k, 0, k, k, list(l)]          # q0, k0, len, lo, hi, tape before
    inside = k >= CUT
    for _ in range(n):
        w, d, s = T[(q, l[k])]
        l[k] = w; k += d; q = s
        cur[2] += 1
        cur[3] = min(cur[3], k); cur[4] = max(cur[4], k)
        if (k >= CUT) != inside:
            segs.append(cur + [q, k, list(l)])
            inside = k >= CUT
            cur = [q, k, 0, k, k, list(l)]
    segs.append(cur + [q, k, list(l)])
    if verbose:
        for (q0, k0, ln, lo, hi, before, q1, k1, after) in segs:
            tag = 'excursion' if hi >= CUT and lo >= CUT - 1 else 'fixed'
            print('%-10s %5d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
                  % (tag, ln, q0, k0, q1, k1, lo, hi))
            print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
            print('    out: %s' % ''.join(map(str, after[lo:hi + 1])))
    return segs


if __name__ == '__main__':
    if len(sys.argv) > 2:
        segment(int(sys.argv[1]), int(sys.argv[2]))
    else:
        check()
        print()
        segs = segment(2, 1, verbose=False)
        print('number of stretches:', len(segs))
        for (q0, k0, ln, lo, hi, _b, q1, k1, _a) in segs:
            print('  %5d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
                  % (ln, q0, k0, q1, k1, lo, hi))
