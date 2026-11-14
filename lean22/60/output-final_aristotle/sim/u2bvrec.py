"""The `P3` row in which the carry, after the absorbing `U(2,8) V(1)`, meets a *second*
`U(2,8) V(1)` instead of a token `U(1,even)` (`ANALYSIS.md` §48, the `12` remaining steps).

The script prints, for

```
0 0 0 . U(2,2) V(1) u . U(2,8) V(1) . u^k . U(2,8) V(1) . u^s . U(1,2m+2) 0
```

the number of steps to the next `B`-event at the new left end and the token word there,
as a function of `k`, `s` and `m`.

Exploratory only; nothing here is machine-checked.
"""

import sys
from u21b import T, U, V, u
from toklib import parse, name


def to_b0(l, k=3, q='B', limit=10 ** 7):
    l = list(l); n = 0
    while n < limit:
        if k == 0 and q == 'B':
            return n, l
        if not (0 <= k < len(l)):
            return ('OUT', n)
        tr = T[(q, l[k])]
        if tr is None:
            return ('HALT', n)
        w, d, s = tr
        l[k] = w; k += d; q = s; n += 1
    return None


def word(k, s, m):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + U(2, 8) + V(1) + u * k
            + U(2, 8) + V(1) + u * s + U(1, 2 * m + 2) + [0])


def show(k, s, m):
    r = to_b0(word(k, s, m))
    if isinstance(r, tuple) and r[0] in ('OUT', 'HALT'):
        print('k=%d s=%d m=%d: %s after %d steps' % (k, s, m, r[0], r[1]))
        return
    n, l = r
    print('k=%d s=%d m=%d: %5d steps, %s'
          % (k, s, m, n, ' '.join(name(x) for x in parse(''.join(map(str, l))))))


if __name__ == '__main__':
    if len(sys.argv) > 3:
        show(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    else:
        for k in (7,):
            for s in range(0, 5):
                for m in range(0, 4):
                    show(k, s, m)
        print()
        for k in range(1, 10):
            show(k, 3, 1)
