"""Collect the token word at every B-event."""
from sim import M
from toklib import parse, fmt

def bevents(maxt=2000000):
    m = M(); minpos = 0; out = []
    while m.t < maxt:
        if not m.step(): raise SystemExit('HALT at %d' % m.t)
        if m.pos < minpos:
            minpos = m.pos
            if m.st == 'B':
                lo, hi = m.bounds()
                w = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, hi+1))
                out.append((m.t, m.pos, parse(w)))
    return out

if __name__ == '__main__':
    import sys
    ev = bevents(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
    for n, (t, p, toks) in enumerate(ev):
        print('%4d t=%-9d p=%-6d %s' % (n, t, p, fmt(toks)))
