def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return 'Halt', a, c
            return 'h', 1, a // 2 + c + 2
        if c % 2 == 0:
            return 'i', 3 * a, c - a + 4
        return 'j', 3 * a + 2, c - a + 1
    r = c % 4
    if r in (0, 2):
        return 'a', a - c - 1, 3 * (c // 2) + 2
    if r == 1:
        if a == c + 1:
            return 'Halt', a, c
        return 'b', a - c - 2, 3 * (c // 2) + 5
    if a == c + 1:
        return 'Halt', a, c
    if a == c + 2:
        return 'e', 3 * c + 8, 1
    if a == c + 3:
        return 'Halt', a, c
    return 'c', a - c - 4, 3 * (c // 2) + 8

def run(a, c, cap=100000):
    n = 0
    while True:
        n += 1
        if n > cap: return n, 'guard'
        kind, a, c = step(a, c)
        if kind == 'Halt': return n, 'halt'
        if a == 1: return n, 'return'

N = 300
for k in (3, 5, 7, 9, 11, 15):
    mism = []
    total = 0
    for a in range(2, N + 1):
        for c in range(1, a):
            l0, _ = run(a, c)
            lk, _ = run(k * a, k * c)
            total += 1
            if l0 != lk:
                mism.append((a, c, l0, lk))
    print(f"k={k} total={total} mismatches={len(mism)}")
    for x in mism[:15]:
        print("   ", x, flush=True)
