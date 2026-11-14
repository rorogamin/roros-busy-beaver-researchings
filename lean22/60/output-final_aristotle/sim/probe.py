"""Probe the 'carry' transducer in isolation.

Set up an artificial tape  0 0 0 | <prefix> <test tokens> u^PAD  with the head in state
B on the first cell of <prefix>, run until the next B-event (head on a new leftmost cell
in state B, first token U(a,b) with a >= 1), and report the resulting token word.
"""
from sim import M, T
from toklib import parse, fmt, word

PAD = 60

def mk(toks, pad=PAD):
    return word(toks) + '042'*pad

def runto(toks, st='B', pad=PAD, maxt=2000000):
    """head at cell 0 in state st, tape = word(toks) + padding; run to next B-event."""
    m = M(); m.st = st; m.pos = 0
    w = mk(toks, pad)
    for i, ch in enumerate(w):
        m.tape[i] = int(ch)
    minpos = 0
    while m.t < maxt:
        if not m.step():
            return ('HALT', m.t)
        if m.pos < minpos:
            minpos = m.pos
            if m.st == 'B':
                lo, hi = m.bounds()
                s = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, hi+1))
                tk = parse(s)
                if tk and tk[0][0] == 'U' and tk[0][1] >= 1:
                    return (tk, m.t, hi)
    return ('TIMEOUT', m.t)

U = lambda a, b: ('U', a, b)
V = lambda c: ('V', c)
u = U(1, 1)

P1 = [U(2, 1), U(4, 1)]
P3 = [U(2, 2), V(1), u]

if __name__ == '__main__':
    tests = []
    for b in range(1, 9):
        tests.append(('U1,%d' % b, [U(1, b)]))
    for b in range(1, 11):
        tests.append(('U2,%d' % b, [U(2, b)]))
    for a in [3, 4, 5, 10, 28]:
        tests.append(('U%d,1' % a, [U(a, 1)]))
    for c in range(1, 8):
        tests.append(('U1,2 V%d' % c, [U(1, 2), V(c)]))
    for c in range(1, 8):
        tests.append(('U2,4 V%d' % c, [U(2, 4), V(c)]))
    for nm, ts in tests:
        for pn, P in (('P1', P1), ('P3', P3)):
            r = runto(P + ts)
            if r[0] in ('HALT', 'TIMEOUT'):
                print('%-4s %-12s -> %s at t=%d' % (pn, nm, r[0], r[1]))
            else:
                print('%-4s %-12s -> t=%-6d %s' % (pn, nm, r[1], fmt(r[0])))
