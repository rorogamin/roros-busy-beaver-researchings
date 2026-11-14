"""Canonical B-events and the token-level transition between consecutive ones."""
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
                toks = parse(w)
                if toks and toks[0][0] == 'U' and toks[0][1] >= 1:
                    out.append((m.t, m.pos, toks))
    return out

if __name__ == '__main__':
    import sys
    ev = bevents(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
    for n in range(len(ev)-1):
        a = ev[n][2]; b = ev[n+1][2]
        # longest common suffix
        s = 0
        while s < len(a) and s < len(b) and a[len(a)-1-s] == b[len(b)-1-s]: s += 1
        print('%4d dt=%-7d  %s   ==>   %s   | suffix %d kept, head changes %s -> %s'
              % (n, ev[n+1][0]-ev[n][0], fmt(a), fmt(b), s,
                 fmt(a[:len(a)-s]), fmt(b[:len(b)-s])))
