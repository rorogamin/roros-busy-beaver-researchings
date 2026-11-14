"""Turning points of the `P1` macro step with `r >= 1` crossed tokens
(`ANALYSIS.md` §36, first row), used to find a stage decomposition for a Lean proof.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T
from p1fr import word0, out0, steps0, word1, out1, steps1


def turning_points(l, q='B', k=3):
    l = list(l)
    prev_dir = 0
    last = 0
    n = 0
    res = [(0, q, k, ''.join(map(str, l)))]
    while True:
        wr, d, s = T[(q, l[k])]
        l[k] = wr
        k += d
        q = s
        n += 1
        if d != prev_dir:
            res.append((n - last, q, k, ''.join(map(str, l))))
            last = n
            prev_dir = d
        if q == 'B' and k == 0:
            break
        if n > 100000:
            break
    res.append((n - last, q, k, ''.join(map(str, l))))
    return res


if __name__ == '__main__':
    print('--- case 0 (absorbing token straight after the inner u), r=1 m=0, %d steps'
          % steps0(1, 0))
    for (d, q, k, l) in turning_points(word0(1, 0)):
        print('  +%-4d %s %2d  %s' % (d, q, k, l))
    print('  expected out:', ''.join(map(str, out0(1, 0))))
    print()
    print('--- case 1 (at least one u intervenes), r=1 s=0 m=0, %d steps' % steps1(1, 0, 0))
    for (d, q, k, l) in turning_points(word1(1, 0, 0)):
        print('  +%-4d %s %2d  %s' % (d, q, k, l))
    print('  expected out:', ''.join(map(str, out1(1, 0, 0))))
