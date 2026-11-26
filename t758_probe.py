import sys, random
from collections import Counter

def step(a, c):
    """exact accelerated map, identical to M_758_Halving844.step"""
    if c + 1 <= a and c % 2 == 0: return a - c - 1, 3*(c//2) + 2, False, 'a'
    if c + 2 <= a and c % 4 == 1: return a - c - 2, 3*(c//2) + 5, False, 'b'
    if c + 4 <= a and c % 4 == 3: return a - c - 4, 3*(c//2) + 8, False, 'c'
    if c + 3 == a and c % 4 == 3: return a, c, True, 'd'
    if c + 2 == a and c % 4 == 3: return 3*c + 8, 1, False, 'e'
    if c + 1 == a and c % 2 == 1: return a, c, True, 'f'
    if c >= a and a % 2 == 0 and c % 2 == 0: return a, c, True, 'g'
    if c >= a and a % 2 == 0 and c % 2 == 1: return 1, a//2 + c + 2, False, 'h'
    if c >= a and a % 2 == 1 and c % 2 == 0: return 3*a, c - a + 4, False, 'i'
    if c >= a and a % 2 == 1 and c % 2 == 1: return 3*a + 2, c - a + 1, False, 'j'
    raise RuntimeError((a, c))

def ht(c0, a, c, cap=40000):
    """halving time, identical to M_758_Halving844.ht"""
    rs = []
    for n in range(1, cap+1):
        a2, c2, h, r = step(a, c)
        rs.append(r)
        if h or a2 == 1 or 2*c2 <= c0: return n, rs
        a, c = a2, c2
    return cap, rs

def counter_str(rs):
    return dict(Counter(rs))

def runs(rs):
    out = []
    for x in rs:
        if out and out[-1][0] == x: out[-1][1] += 1
        else: out.append([x, 1])
    return out

def phases(rs):
    out = []
    for x in rs:
        t = 'L' if x in 'abce' else 'J'
        if out and out[-1][0] == t: out[-1][1] += 1
        else: out.append([t, 1])
    return out

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'trace'
    if mode == 'trace':
        k = int(sys.argv[2]); c = int(sys.argv[3])
        a = 2*3**k - 1
        n, rs = ht(c, a, c)
        print('k=%d c=%d T=%d' % (k, c, n))
        print('rules:', counter_str(rs))
        print('runs:', runs(rs)[:40])
        print('phases:', phases(rs)[:40])
    elif mode == 'sweep':
        k = int(sys.argv[2]); lo = int(sys.argv[3]); hi = int(sys.argv[4])
        a = 2*3**k - 1
        best = (0, 0, [])
        hist = Counter()
        for c in range(lo, hi+1):
            n, rs = ht(c, a, c)
            hist[tuple(x[0] for x in phases(rs))] += 1
            if n > best[0]: best = (n, c, phases(rs))
        print('k=%d c in [%d,%d] maxT=%d at c=%d phases=%s' % (k, lo, hi, best[0], best[1], best[2]))
        for sh, cnt in hist.most_common(12):
            print('   ', ''.join(sh), cnt)
    elif mode == 'maxphases':
        k = int(sys.argv[2]); lo = int(sys.argv[3]); hi = int(sys.argv[4])
        a = 2*3**k - 1
        best = (0, 0, [])
        for c in range(lo, hi+1):
            n, rs = ht(c, a, c)
            ph = phases(rs)
            if len(ph) > best[0]: best = (len(ph), c, ph)
        print('k=%d max #phases=%d at c=%d: %s' % (k, best[0], best[1], best[2]))

if __name__ == '__main__':
    main()
