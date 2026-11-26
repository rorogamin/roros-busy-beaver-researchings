import random

def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return None
            return (1, a // 2 + c + 2)
        else:
            if c % 2 == 0:
                return (3 * a, c - a + 4)
            return (3 * a + 2, c - a + 1)
    else:
        r = c % 4
        if r in (0, 2):
            return (a - c - 1, 3 * (c // 2) + 2)
        if r == 1:
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


def run(c0, a, c, cap=200000):
    n = 0
    path = [(a, c)]
    while True:
        r = step(a, c)
        n += 1
        if r is None:
            return n, 'halt', path
        a, c = r
        path.append((a, c))
        if a == 1:
            return n, 'a1', path
        if 2 * c <= c0:
            return n, 'c2', path
        if n > cap:
            return n, 'cap', path


best = (0, None)
for k in range(0, 9):
    a = 2 * 3 ** k - 1
    for c in range(1, 2 * 3 ** k):
        n, why, _ = run(c, a, c)
        if n > best[0]:
            best = (n, (k, c, why))
print("exhaustive k<=8 max:", best)

for k in (10, 20, 50, 100, 200, 292):
    a = 2 * 3 ** k - 1
    lim = 2 * 3 ** k
    cands = set()
    for c in (1, 2, 3, 4, 5, 7, 8, 9, 2000, 2047, 4096, 6561, lim - 1, lim - 2, lim - 3,
              lim // 2, lim // 3, lim // 4, 3 ** k, 3 ** k - 1, 3 ** k + 1):
        if 1 <= c < lim:
            cands.add(c)
    for c in range(1, 200):
        cands.add(c)
    random.seed(7)
    for _ in range(4000):
        cands.add(random.randrange(1, lim))
    for _ in range(2000):
        cands.add(random.randrange(1, min(lim, 10 ** 6)))
    for c in sorted(cands):
        n, why, _ = run(c, a, c)
        if n > best[0]:
            best = (n, (k, c, why))
    print("after k =", k, "max:", best)

print("FINAL max:", best)
