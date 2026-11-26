"""Measure phase / cycle counts of the accelerated #758 map.

Phase = maximal same-region run (L: c < a, J: a <= c).  Stops exactly as hrun:
halt, a' = 1, or 2*c' <= c0.
"""
import sys

def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return None
            return (1, a // 2 + c + 2)
        if c % 2 == 0:
            return (3 * a, c - a + 4)
        return (3 * a + 2, c - a + 1)
    if c % 4 == 0 or c % 4 == 2:
        return (a - c - 1, 3 * (c // 2) + 2)
    if c % 4 == 1:
        if a == c + 1:
            return None
        return (a - c - 2, 3 * ((c - 1) // 2) + 5)
    if a == c + 1:
        return None
    if a == c + 2:
        return (3 * c + 8, 1)
    if a == c + 3:
        return None
    return (a - c - 4, 3 * ((c - 1) // 2) + 8)

def run(a, c, cap=40000):
    """Return (steps, nL, nJ, phase_lens, why)."""
    c0 = c
    t = 0
    lens = []
    cur = None  # 'L' or 'J'
    nL = nJ = 0
    why = 'cap'
    while t < cap:
        reg = 'J' if a <= c else 'L'
        if cur is None:
            cur = reg
            lens.append(0)
            if reg == 'L':
                nL += 1
            else:
                nJ += 1
        elif reg != cur:
            cur = reg
            lens.append(0)
            if reg == 'L':
                nL += 1
            else:
                nJ += 1
        lens[-1] += 1
        nx = step(a, c)
        if nx is None:
            why = 'halt'
            t += 1
            break
        a, c = nx
        t += 1
        if a == 1:
            why = 'a1'
            break
        if 2 * c <= c0:
            why = 'c-halved'
            break
    return t, nL, nJ, lens, why

def main():
    # 1. exhaustive small k, sampled large k
    best = (0, None)
    worst = None
    k_max = 8
    for k in range(0, k_max + 1):
        m = 2 * 3 ** k - 1
        for c in range(1, 2 * 3 ** k):
            t, nL, nJ, lens, why = run(m, c)
            tag = (nL, nJ)
            if nJ > best[0]:
                best = (nJ, (k, c, t, nL, nJ, why, lens))
            if worst is None or (nL, nJ, t) > (worst[0], worst[1], worst[2]):
                worst = (nL, nJ, t, k, c, why, lens)
    print('exhaustive k<=%d: max NJ %d at %s' % (k_max, best[0], best[1]))
    print('exhaustive k<=%d: worst (nL,nJ,t) %s' % (k_max, worst[:6]))

    # 2. sampled large k
    import random
    random.seed(12345)
    mx = (0, None)
    mxnL = (0, None)
    for k in [10, 20, 40, 80, 120, 160, 200, 240, 280, 292]:
        m = 2 * 3 ** k - 1
        cs = set([1, 2, 3, 2 * 3 ** k - 2, 2047, 471656, 3583, 8191, 65535])
        while len(cs) < 400:
            cs.add(random.randrange(1, 2 * 3 ** k))
        for c in cs:
            if not (1 <= c < 2 * 3 ** k):
                continue
            t, nL, nJ, lens, why = run(m, c)
            if nJ > mx[0]:
                mx = (nJ, (k, c, t, nL, nJ, why, lens))
            if nL > mxnL[0]:
                mxnL = (nL, (k, c, t, nL, nJ, why, lens))
    print('sampled large k: max NJ %d at %s' % (mx[0], mx[1]))
    print('sampled large k: max NL %d at %s' % (mxnL[0], mxnL[1]))

    # 3. small states: is the phase count bounded in general?
    bester = (0, None)
    for a in range(1, 400):
        for c in range(1, 400):
            t, nL, nJ, lens, why = run(a, c)
            if nL > bester[0]:
                bester = (nL, (a, c, t, nL, nJ, why, lens))
    print('small states a,c<400: max NL %d at %s' % (bester[0], bester[1]))

    # 4. check alternation on everything seen
    bad = 0
    for k in range(0, 7):
        m = 2 * 3 ** k - 1
        for c in range(1, 2 * 3 ** k):
            t, nL, nJ, lens, why = run(m, c)
            if not (nL in (nJ, nJ + 1) and nJ in (nL, nL - 1)):
                bad += 1
    print('alternation violations on family k<=6:', bad)

if __name__ == '__main__':
    main()
