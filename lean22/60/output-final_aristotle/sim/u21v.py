"""The `P3` macro step with a crossed `U(2,1)`, an absorbing `U(1,even)` and a `V` after it
(the last of the two "crossed exponent 2 and a V" rows of `ANALYSIS.md` §31).

The script probes the configuration

    0 0 0 . U(2,2) V(1) u . u^r . U(2,1) . u^s . U(1,2m+2) . V(2c+5) . u^w . U(1,2m'+2) 0

runs the machine until the head returns to a new leftmost cell in state `B`, and prints the
resulting tape word together with the number of steps, so that a rule can be read off.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T, U, V, u
from toklib import parse, fmt


def word(r, s, m, c, w):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + u * r + U(2, 1) + u * s + U(1, 2 * m + 2)
            + V(2 * c + 5) + u * w + U(1, 2 * mp_default) + [0])


mp_default = 2


def word_full(r, s, m, c, w, mp):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + u * r + U(2, 1) + u * s + U(1, 2 * m + 2)
            + V(2 * c + 5) + u * w + U(1, 2 * mp + 2) + [0])


def run_to_left_end(l, verbose=False):
    """Run from state B on cell 3 until the head is in state B on cell 0."""
    l = list(l)
    q, k, n = 'B', 3, 0
    while True:
        if q == 'B' and k == 0:
            return n, l
        t = T[(q, l[k])]
        if t is None:
            return None, 'HALT'
        wr, d, s = t
        l[k] = wr
        k += d
        q = s
        n += 1
        if not (0 <= k < len(l)):
            return None, 'OUT'
        if n > 100000:
            return None, 'LOOP'


def show(r, s, m, c, w, mp):
    n, out = run_to_left_end(word_full(r, s, m, c, w, mp))
    if n is None:
        print('r=%d s=%d m=%d c=%d w=%d mp=%d -> %s' % (r, s, m, c, w, mp, out))
        return None
    print('r=%d s=%d m=%d c=%d w=%d mp=%d -> %4d steps   %s'
          % (r, s, m, c, w, mp, n, fmt(parse(''.join(map(str, out))))))
    return n, out


if __name__ == '__main__':
    base = show(0, 0, 0, 0, 0, 0)
    for (r, s, m, c, w, mp) in [(1, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 0), (0, 0, 1, 0, 0, 0),
                                (0, 0, 0, 1, 0, 0), (0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, 1),
                                (2, 1, 1, 1, 1, 1)]:
        show(r, s, m, c, w, mp)
