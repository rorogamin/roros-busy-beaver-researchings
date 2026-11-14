"""Does a long 4-run really host a *copy* of the machine's own computation?

Set up   0 0 0 | P3-prefix  U(a,1)  u^pad   with the head in state B on the first
cell, run to the next B-event, and record every moment at which the head is in
state B inside the region originally occupied by the token U(a,1), at a position
that is a new minimum among such visits.  Print the token word from the head
rightwards at each such moment.
"""
import sys
from sim import M
from toklib import parse, fmt, word
from probe import U, u, P1, P3, mk
from be2 import bevents


def inner(a, prefix=P3, pad=60, maxt=4000000):
    toks = prefix + [U(a, 1)]
    w = mk(toks, pad)
    m = M(); m.st = 'B'; m.pos = 0
    for i, ch in enumerate(w):
        m.tape[i] = int(ch)
    start = len(word(prefix))          # first cell of the U(a,1) token
    end = start + a + 2                # one past it
    minpos = 0
    out = []
    seen = end + 1
    entered = False
    while m.t < maxt:
        if not m.step():
            out.append(('HALT', m.t)); break
        if m.pos >= end:
            entered = True
        if entered and m.st == 'B' and start <= m.pos < seen:
            seen = m.pos
            s = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, len(w)))
            out.append((m.t, m.pos - start, parse(s)))
        if m.pos < minpos:
            minpos = m.pos
            if m.st == 'B':
                s = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, len(w)))
                out.append(('DONE', m.t, parse(s)))
                break
    return out


if __name__ == '__main__':
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    ev = bevents(400000)
    W = [e[2] for e in ev]
    for i, Wi in enumerate(W[:12]):
        print('W_%-3d %s' % (i, fmt(Wi)))
    print('---')
    res = inner(a)
    for r in res:
        if r[0] == 'HALT':
            print(r); continue
        if r[0] == 'DONE':
            print('DONE t=%d  %s' % (r[1], fmt(r[2]))); continue
        t, off, tk = r
        print('t=%-7d off=%-5d %s' % (t, off, fmt(tk)[:160]))
