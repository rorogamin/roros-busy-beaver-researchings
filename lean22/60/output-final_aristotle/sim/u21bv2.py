"""Stage decomposition of the rule of `ANALYSIS.md` §36, third row
(a crossed `U(2,1)`, an absorbing `U(2,2m+4)` and a `V(1)` after it).

This prints the configuration (state, head position, tape word) at the cumulative
step counts of the twenty-six stages the Lean proof in
`RequestProject/CarryU21bV.lean` uses, so the intermediate words in that proof can be
read off and checked.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T
from u21bv import word, out, steps


def trace(q, k, l, n):
    l = list(l)
    for _ in range(n):
        w, d, s = T[(q, l[k])]
        l[k] = w
        k += d
        q = s
    return q, k, l


def durations(r, m, t, mp):
    return [22, 3, 4, 3 * r, 4, 8 * m + 8, 12, 3 * t + 6, 10 * mp + 14, 3 * t + 6, 2,
            3 * t + 6, 10 * mp + 24, 3 * t + 3, 1, 2 * m + 5, 3 * r + 3, 1, 1, 1, 2, 6,
            2, 6, 14, 11]


def show(r, m, t, mp):
    l = word(r, m, t, mp)
    print('params r=%d m=%d t=%d mp=%d, total %d, sum %d'
          % (r, m, t, mp, steps(r, m, t, mp), sum(durations(r, m, t, mp))))
    q, k = 'B', 3
    cum = 0
    print('  %3d  %s %2d  %s' % (cum, q, k, ''.join(map(str, l))))
    for i, d in enumerate(durations(r, m, t, mp)):
        q, k, l = trace(q, k, l, d)
        cum += d
        print('  %3d  %s %2d  %s   (after stage %d)'
              % (cum, q, k, ''.join(map(str, l)), i + 1))
    print('  expected out:', ''.join(map(str, out(r, m, t, mp))))


if __name__ == '__main__':
    show(1, 1, 1, 1)
    show(0, 0, 0, 0)
