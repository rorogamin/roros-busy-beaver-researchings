import random

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

def run(a, c, cap=200000):
    n = 0
    while True:
        n += 1
        if n > cap: return n, 'guard'
        kind, a, c = step(a, c)
        if kind == 'Halt': return n, 'halt'
        if a == 1: return n, 'return'

random.seed(758)
for bits in (64, 128, 256, 463, 700, 1000):
    samples = 2000 if bits <= 256 else 600
    worst = {}
    for _ in range(samples):
        a = random.getrandbits(bits) | (1 << (bits - 1))
        c = random.getrandbits(bits - 1) | (1 << (bits - 2))
        # keep a > c roughly, like a post-j state
        if a <= c:
            a, c = c + 1, c
        k = max(1, int(round(bits * 0.63093)))
        perturbs = {
            '(+2,+4k)': (2, 4 * k),
            '(+2,+0)': (2, 0),
            '(+1,0)': (1, 0),
            '(0,+1)': (0, 1),
            '(+2,-4k)': (2, -4 * k),
        }
        l0, _ = run(a, c)
        for name, (da, dc) in perturbs.items():
            a2, c2 = a + da, c + dc
            if a2 < 1 or c2 < 1:
                continue
            l1, _ = run(a2, c2)
            d = abs(l1 - l0)
            if name not in worst or d > worst[name][0]:
                worst[name] = (d, a, c, l0, l1)
    print(f"bits={bits}")
    for name, w in worst.items():
        print(f"  {name}: max|dL|={w[0]}  L={w[3]},{w[4]}  (a,c bits ~{bits})")
