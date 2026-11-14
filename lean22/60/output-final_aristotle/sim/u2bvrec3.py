"""The `P3` row in which the carry meets a second `U(2,8) V(1)` and only three tokens `u`
follow it — the eight-step shape of `ANALYSIS.md` §48.

```
0 0 0 . U(2,2) V(1) u . U(2,8) V(1) . u^7 . U(2,8) V(1) . u^3 . U(1,2m+2) 0
       --(1305 + 100m) steps-->
   U(2,1) U(4,1) . u u . U(2,2) V(1) . u^9 . U(1,2) . V(2m+19) 0
```

Everything except the final run of `2`s is fixed here, so the computation splits into
stretches in which the head stays inside the first `74` cells and excursions into the run
of `2`s.  The script checks the rule and prints the split.

Exploratory only; nothing here is machine-checked.
"""

import sys
from u21b import T, U, V, u

CUT = 74


def word(m):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + U(2, 8) + V(1) + u * 7
            + U(2, 8) + V(1) + u * 3 + U(1, 2 * m + 2) + [0])


def out(m):
    return (U(2, 1) + U(4, 1) + u + u + U(2, 2) + V(1) + u * 9 + U(1, 2)
            + V(2 * m + 19) + [0])


def steps(m):
    return 1305 + 100 * m


def check(mrange=range(0, 6)):
    bad = 0
    for m in mrange:
        l = list(word(m)); q, k = 'B', 3
        for _ in range(steps(m)):
            tr = T[(q, l[k])]
            if tr is None:
                print('HALT m=%d' % m); bad += 1; break
            w, d, s = tr
            l[k] = w; k += d; q = s
            if not (0 <= k < len(l)):
                print('OUT m=%d' % m); bad += 1; break
        else:
            if (q, k) != ('B', 0) or l != out(m):
                print('MISMATCH m=%d -> %s%d' % (m, q, k)); bad += 1
    print('mismatches:', bad)


def segment(m, verbose=True):
    l = list(word(m)); q, k = 'B', 3
    segs = []
    cur = [q, k, 0, k, k, list(l)]
    inside = k >= CUT
    for _ in range(steps(m)):
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
            tag = 'excursion' if lo >= CUT - 1 else 'fixed'
            print('%-10s %5d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
                  % (tag, ln, q0, k0, q1, k1, lo, hi))
            print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
            print('    out: %s' % ''.join(map(str, after[lo:hi + 1])))
    return segs


if __name__ == '__main__':
    if len(sys.argv) > 1:
        segment(int(sys.argv[1]))
    else:
        check()
        print()
        segs = segment(2, verbose=False)
        print('number of stretches:', len(segs))
        for (q0, k0, ln, lo, hi, _b, q1, k1, _a) in segs:
            print('  %5d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
                  % (ln, q0, k0, q1, k1, lo, hi))
