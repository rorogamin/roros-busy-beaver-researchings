import random, sys
from t758_probe import step

def ht_dq(c0, a, c, cap=40000):
    q0 = a + 2*c
    q = q0
    for n in range(1, cap+1):
        a2, c2, h, r = step(a, c)
        q = a2 + 2*c2
        if h or a2 == 1 or 2*c2 <= c0:
            return n, q - q0
        a, c = a2, c2
    return cap, q - q0

def main():
    random.seed(12345)
    bestT = (0, (0, 0)); bestDQ = (0, (0, 0, 0))
    ks = [1,2,3,5,8,13,21,34,55,89,144,200,233,255,270,280,285,289,290,291,292]
    for k in ks:
        a = 2*3**k - 1
        hi = min(2*3**k - 1, 800)
        for c in range(1, hi+1):
            t, dq = ht_dq(c, a, c)
            if t > bestT[0]: bestT = (t, (k, c))
            if dq > bestDQ[0]: bestDQ = (dq, (k, c, t))
    print('exhaustive c<=800: maxT=%d (k=%d c=%d) ; maxDQ=%d (k=%d c=%d T=%d)'
          % (bestT[0], bestT[1][0], bestT[1][1],
             bestDQ[0], bestDQ[1][0], bestDQ[1][1], bestDQ[1][2]), flush=True)
    for k in [289, 290, 291, 292]:
        a = 2*3**k - 1
        for _ in range(600):
            c = random.randrange(1, 2*3**k)
            t, dq = ht_dq(c, a, c)
            if t > bestT[0]: bestT = (t, (k, c))
            if dq > bestDQ[0]: bestDQ = (dq, (k, c, t))
    print('plus random large c: maxT=%d (k=%d c=%d) ; maxDQ=%d (k=%d c=%d T=%d)'
          % (bestT[0], bestT[1][0], bestT[1][1],
             bestDQ[0], bestDQ[1][0], bestDQ[1][1], bestDQ[1][2]), flush=True)
    # also scan every step of every chain (not just post-j starts)
    bestS = (0, (0, 0, 0))
    for k in [50, 100, 200, 289, 292]:
        a0 = 2*3**k - 1
        for c in range(1, 400):
            a, cc = a0, c
            for _ in range(2000):
                t, dq = ht_dq(cc, a, cc)
                if t > bestS[0]: bestS = (t, (k, c, 0))
                a2, c2, h, r = step(a, cc)
                if h or a2 == 1: break
                a, cc = a2, c2
    print('all states of sampled chains: maxT=%d (k=%d c=%d)' % (bestS[0], bestS[1][0], bestS[1][1]))

if __name__ == '__main__':
    main()
