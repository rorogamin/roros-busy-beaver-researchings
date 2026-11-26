import sys
from t758_probe import step, ht, phases, runs

def detail(k, c):
    a = 2*3**k - 1
    c0 = c
    Q0 = a + 2*c
    st = []
    n = 0
    while True:
        n += 1
        a2, c2, h, r = step(a, c)
        if h or a2 == 1 or 2*c2 <= c0:
            st.append((n, r, a, c, a+2*c))
            break
        st.append((n, r, a, c, a+2*c))
        a, c = a2, c2
        if n > 40000: break
    return a, c0, n, st

def summarize(k, c):
    a, c0, n, st = detail(k, c)
    # phase boundaries
    ph = phases([s[1] for s in st])
    idx = 0
    out = []
    for typ, ln in ph:
        s = st[idx]
        out.append((typ, ln, s[2], s[3], s[4]))
        idx += ln
    return n, out

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'detail':
        k = int(sys.argv[2]); c = int(sys.argv[3])
        n, out = summarize(k, c)
        print('k=%d c=%d T=%d  #phases=%d' % (k, c, n, len(out)))
        Q0 = 2*3**k - 1 + 2*c
        for typ, ln, a, cc, Q in out:
            print('  %s len=%-4d a=%-22s c=%-22s a/Q=%.4f c/Q=%.4f' % (
                typ, ln, str(a)[:22], str(cc)[:22], a/Q, cc/Q))
    elif mode == 'stats':
        k = int(sys.argv[2]); lo = int(sys.argv[3]); hi = int(sys.argv[4])
        bestT = (0,0); bestPh = (0,0); bestTail=(0,0)
        for c in range(lo, hi+1):
            n, out = summarize(k, c)
            tail = n - out[0][1]
            if n > bestT[0]: bestT = (n, c)
            if len(out) > bestPh[0]: bestPh = (len(out), c)
            if tail > bestTail[0]: bestTail = (tail, c)
        print('k=%d c in [%d,%d]: maxT=%d@c=%d  max#phases=%d@c=%d  maxtail=%d@c=%d'
              % (k, lo, hi, bestT[0], bestT[1], bestPh[0], bestPh[1], bestTail[0], bestTail[1]))
