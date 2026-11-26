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
    if c % 4 in (0, 2):
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


def walk(k, c0, limit=20000):
    """Return (T, hits) with hits = [(idx, a, c)] of gap-4 L states."""
    a, c = 2 * 3 ** k - 1, c0
    hits = []
    for i in range(limit):
        if c < a and a == c + 4:
            hits.append((i, a, c))
        nxt = step(a, c)
        if nxt is None:
            return i, hits, True
        a2, c2 = nxt
        if a2 == 1 or 2 * c2 <= c0:
            return i + 1, hits, False
        a, c = a2, c2
    return limit, hits, None


best = 0
example = None
nonmono = 0
total_hits = 0
runs = 0
for k in range(0, 9):
    for c0 in range(1, 2 * 3 ** k):
        runs += 1
        T, hits, halted = walk(k, c0)
        total_hits += len(hits)
        if len(hits) > best:
            best, example = len(hits), (k, c0, T, hits)
        cs = [h[2] for h in hits]
        for x, y in zip(cs, cs[1:]):
            if y <= x:
                nonmono += 1
print('runs=%d  max_hits=%d  total_hits=%d  nonmono_c_pairs=%d' % (runs, best, total_hits, nonmono))
if example:
    print('example k=%d c0=%d T=%d' % (example[0], example[1], example[2]))
    for idx, a, c in example[3][:10]:
        print('   idx=%-5d a=%d c=%d (a-c=4, c even=%s)' % (idx, a, c, c % 2 == 0))
else:
    print('no gap-4 L state ever reached')

# large-k samples
import random
random.seed(11)
mx = 0
for _ in range(400):
    k = random.randint(9, 120)
    c0 = random.randint(1, 2 * 3 ** k - 1)
    T, hits, _ = walk(k, c0, 60000)
    if len(hits) > mx:
        mx = len(hits)
        print('sample max hits=%d at k=%d c0=%d T=%d' % (len(hits), k, c0, T))
print('sample_max_hits=%d' % mx)
