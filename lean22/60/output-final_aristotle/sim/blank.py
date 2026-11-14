"""Probe the carry when it runs off the *blank* right end (`ANALYSIS.md` §53).

Sets up the artificial tape  0 0 0 | <prefix> u^N  with the head in state B on the first
cell of <prefix> and *no* padding beyond the run of `u`s, and runs to the next B-event.
The two families it prints,

    P1, u^N   ->  U2,2 u U2,1 u^(N+1)   in 47 + 12N steps
    P3, u^N   ->  U2,1 U4,1 u^(N+2)     in 59 + 12N steps

are the two rules `rule_P1_blank` and `rule_P3_blank` of `RequestProject/BlankRight.lean`.
With `--trace N` the script instead dumps the cell-by-cell trace of the `P3` case, which
is where the nine-stage decomposition used in the Lean proof was read off.

Exploratory only; nothing here is machine-checked.
"""

import sys

from probe import runto, P1, P3, u
from sim import M
from toklib import fmt, word


def table(maxN=8):
    for pn, P in (('P1', P1), ('P3', P3)):
        for N in range(maxN + 1):
            r = runto(P + [u] * N, pad=0)
            if r[0] in ('HALT', 'TIMEOUT'):
                print('%s N=%d -> %s at t=%d' % (pn, N, r[0], r[1]))
            else:
                print('%s N=%-2d t=%-6d %s' % (pn, N, r[1], fmt(r[0])))


def trace(N, prefix=P3, steps=None):
    if steps is None:
        steps = 60 + 12 * N
    w = '000' + word(prefix + [u] * N) + '0000'
    m = M()
    m.st = 'B'
    m.pos = 3
    for i, ch in enumerate(w):
        m.tape[i] = int(ch)
    for t in range(steps):
        s = ''.join(str(m.tape.get(i, 0)) for i in range(max(len(w), m.pos + 1)))
        print('%3d %s %s %2d' % (t, m.st, s[:m.pos] + '[' + s[m.pos] + ']' + s[m.pos + 1:],
                                 m.pos))
        if not m.step():
            print('HALT')
            return


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == '--trace':
        trace(int(sys.argv[2]))
    else:
        table()
