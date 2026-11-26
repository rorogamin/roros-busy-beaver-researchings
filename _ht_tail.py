import random
from _ht_scan import step


def walk(c0, a, c, cap=200000):
    """Return (t, first phase length, exit, tail ratio window)."""
    n = 0
    first_len = 0
    tag0 = 'J' if a <= c else 'L'
    in_first = True
    ratios = []
    while True:
        r = step(a, c)
        n += 1
        if r is None:
            return n, first_len, 'halt', ratios
        a2, c2 = r
        tag = 'J' if a <= c else 'L'
        if in_first:
            if tag != tag0:
                in_first = False
            else:
                first_len = n
        a, c = a2, c2
        if a == 1:
            return n, first_len, 'a1', ratios
        if 2 * c <= c0:
            return n, first_len, 'c2', ratios
        if not in_first and c > 0:
            ratios.append(a / c)
        if n > cap:
            return n, first_len, 'cap', ratios


rows = []
for k in (7, 30, 60, 100, 150, 200, 250, 292):
    lim = 2 * 3 ** k
    a0 = lim - 1
    random.seed(k)
    cs = [random.randrange(1, lim) for _ in range(1500)]
    cs += [1, 2, 3, 5, 7, 24, 2000, lim - 1, lim // 2, lim // 3, 3 ** k, 3 ** k + 1]
    best = None
    for c in cs:
        if not (1 <= c < lim):
            continue
        t, fl, ex, rs = walk(c, a0, c)
        if best is None or t > best[0]:
            best = (t, c, fl, ex, rs)
    t, c, fl, ex, rs = best
    print("k=%3d  T=%4d  firstphase=%4d  tail=%4d  exit=%s  c=%d  ratio=[%.3f, %.2f]"
          % (k, t, fl, t - fl, ex, c % 100000, min(rs) if rs else 0, max(rs) if rs else 0))

# how often is the exit a1?
cnt = {'a1': 0, 'c2': 0, 'halt': 0, 'cap': 0}
maxtail = 0
for k in (10, 40, 80, 292):
    lim = 2 * 3 ** k
    random.seed(99 + k)
    for _ in range(300):
        c = random.randrange(1, lim)
        t, fl, ex, rs = walk(c, lim - 1, c)
        cnt[ex] = cnt.get(ex, 0) + 1
        maxtail = max(maxtail, t - fl)
print("exit counts:", cnt, " max tail seen:", maxtail)
