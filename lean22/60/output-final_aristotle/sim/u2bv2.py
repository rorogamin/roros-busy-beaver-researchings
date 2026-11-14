"""The `P3` macro step with a `V` after an absorbing `U(2,8)` (ANALYSIS.md §36, second row).

In the real orbit the absorbing token of this census row is always `U(2,8)`; the head makes
five passes.  The script also shows how irregular the behaviour is in the exponent of the
absorbing token: `U(2,4)` halts, and `U(2,6)`, `U(2,8)`, `U(2,10)`, `U(2,12)` give four
different shapes of output.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T, U, V, u
from toklib import parse, name


def run_win(q, k, l, n):
    l = list(l)
    for _ in range(n):
        t = T[(q, l[k])]
        if t is None: return ('HALT',)
        w, d, s = t
        l[k] = w; k += d; q = s
        if not (0 <= k < len(l)): return ('OUT',)
    return q, k, l


def word(t, mp):
    return [0, 0, 0] + U(2, 2) + V(1) + u + U(2, 8) + V(1) + u * (t + 2) + U(1, 2 * mp + 2) + [0]


def out(t, mp):
    return U(2, 1) + U(4, 1) + u + u + U(2, 2) + V(1) + u * t + U(1, 2 * mp + 12) + [0]


def steps(t, mp): return 403 + 30 * t + 50 * mp


def to_b0(l, k=3, q='B', limit=10 ** 6):
    l = list(l); n = 0
    while n < limit:
        if k == 0 and q == 'B': return n, l
        if not (0 <= k < len(l)): return ('OUT', n)
        t = T[(q, l[k])]
        if t is None: return ('HALT', n)
        w, d, s = t
        l[k] = w; k += d; q = s; n += 1
    return None


if __name__ == '__main__':
    bad = 0
    for t in range(4):
        for mp in range(4):
            res = run_win('B', 3, word(t, mp), steps(t, mp))
            if res != ('B', 0, out(t, mp)):
                bad += 1; print('MISMATCH', t, mp, res[:2])
    print('mismatches:', bad)
    print()
    print('dependence on the exponent of the absorbing token (t = 2, m\' = 0):')
    for m in range(0, 5):
        w = ([0, 0, 0] + U(2, 2) + V(1) + u + U(2, 2 * m + 4) + V(1) + u * 4 + U(1, 2) + [0])
        r = to_b0(w)
        if isinstance(r, tuple) and r[0] in ('OUT', 'HALT'):
            print('  U(2,%d): %s after %d steps' % (2 * m + 4, r[0], r[1]))
        else:
            n, l = r
            print('  U(2,%d): %d steps, %s' % (2 * m + 4, n,
                  ' '.join(name(x) for x in parse(''.join(map(str, l))))))
