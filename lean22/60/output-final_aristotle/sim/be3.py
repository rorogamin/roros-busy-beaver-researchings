"""For each canonical B-event transition, measure how far right the head travels,
and express the transition as a *local* token rewrite: prefix in -> prefix out."""
from sim import M
from toklib import parse, fmt, word, name

def run(maxt):
    m = M(); minpos = 0; ev = []
    while m.t < maxt:
        if not m.step(): raise SystemExit('HALT at %d' % m.t)
        if m.pos < minpos:
            minpos = m.pos
            if m.st == 'B':
                lo, hi = m.bounds()
                w = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, hi+1))
                toks = parse(w)
                if toks and toks[0][0] == 'U' and toks[0][1] >= 1:
                    ev.append((m.t, m.pos, toks))
    return ev

def run_marked(maxt):
    """like run, but also record max position reached between consecutive events"""
    m = M(); minpos = 0; ev = []; hi_since = m.pos
    while m.t < maxt:
        if not m.step(): raise SystemExit('HALT at %d' % m.t)
        hi_since = max(hi_since, m.pos)
        if m.pos < minpos:
            minpos = m.pos
            if m.st == 'B':
                lo, hi = m.bounds()
                w = ''.join(str(m.tape.get(i, 0)) for i in range(m.pos, hi+1))
                toks = parse(w)
                if toks and toks[0][0] == 'U' and toks[0][1] >= 1:
                    ev.append((m.t, m.pos, toks, hi_since, hi))
                    hi_since = m.pos
    return ev

if __name__ == '__main__':
    import sys
    ev = run_marked(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
    rules = {}
    for n in range(len(ev)-1):
        t0, p0, a, _, hi0 = ev[n]
        t1, p1, b, hs, hi1 = ev[n+1]
        # cells of the old tape (from p0) that were touched: p0 .. hs
        reach = hs - p0            # number of cells right of head reached
        # split old token list at the reach point
        i = 0; acc = 0
        wl = [len(word([t])) for t in a]
        while i < len(a) and acc + wl[i] <= reach:
            acc += wl[i]; i += 1
        # i = index of token containing the deepest cell reached
        untouched = len(a) - (i+1)
        print('%4d dt=%-7d reach=%-5d len=%-5d untouched_toks=%-4d  IN %s | %s' %
              (n, t1-t0, reach, hi0-p0+1, untouched, fmt(a[:i+1]), fmt(a[i+1:])))
