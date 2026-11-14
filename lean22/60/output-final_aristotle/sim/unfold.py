"""Find the next instances of the fractal unfolding rule (`ANALYSIS.md` §20, §55).

For a token `U(a,1)` with `a = 3j+1` the carry meeting it unfolds it into a copy of the
tape at the `j`-th `B`-event.  `unfold_U4` and `unfold_U10` in `RequestProject/Carry.lean`
are the two smallest instances; this script searches for the next ones.

For each `a` it tries tails `u^k · U(1,2)` of growing length, runs the machine from the
window

    0 0 0 | U(2,2) V(1) u | U(a,1) | tail | 0

with the head in state `B` on the first non-blank cell, and stops at the next `B`-event
three cells further left.  It reports the tail that works, the resulting token word, the
number of steps, and — the condition for the result to be a *window* rule — whether the
head stayed inside the window.

Exploratory only; nothing here is machine-checked.
"""

import sys

from sim import M
from toklib import parse, fmt, word

U = lambda a, b: ('U', a, b)
V = lambda c: ('V', c)
u = U(1, 1)
P3 = [U(2, 2), V(1), u]


def attempt(a, k, maxt=2000000):
    """Return (steps, out_tokens, max_pos, window_len) or None."""
    toks = P3 + [U(a, 1)] + [u] * k + [U(1, 2)]
    w = '000' + word(toks) + '0'
    m = M()
    m.st = 'B'
    m.pos = 3
    for i, ch in enumerate(w):
        m.tape[i] = int(ch)
    hi = m.pos
    while m.t < maxt:
        if not m.step():
            return None
        hi = max(hi, m.pos)
        if m.pos == 0 and m.st == 'B':
            s = ''.join(str(m.tape.get(i, 0)) for i in range(0, len(w)))
            return (m.t, parse(s), hi, len(w))
        if m.pos < 0:
            return None
    return None


if __name__ == '__main__':
    for a in [int(x) for x in (sys.argv[1:] or ['4', '7', '10', '13', '16'])]:
        for k in range(0, 8):
            r = attempt(a, k)
            if r is None:
                continue
            steps, out, hi, wl = r
            ok = 'inside' if hi < wl else 'LEAVES WINDOW'
            print('a=%-3d tail=u^%d U1,2   steps=%-7d %-12s out = %s'
                  % (a, k, steps, ok, fmt(out)))
            break
        else:
            print('a=%-3d no tail of the tried shape works' % a)
