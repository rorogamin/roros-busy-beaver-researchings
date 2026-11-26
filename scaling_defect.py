import random, math

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

def run(a, c, cap=500000):
    n = 0
    while True:
        n += 1
        if n > cap: return n
        kind, a, c = step(a, c)
        if kind == 'Halt': return n
        if a == 1: return n

random.seed(758)
for bits in (64, 128, 256, 463, 700, 1000):
    samples = 1500 if bits <= 256 else 500
    worst = {k: (0, 0, 0, 0) for k in (2, 3, 4, 5)}
    for _ in range(samples):
        a = random.getrandbits(bits) | (1 << (bits - 1))
        c = random.getrandbits(bits - 1) | (1 << (bits - 2))
        if a <= c:
            a, c = c + 1, c
        l0 = run(a, c)
        for k in (2, 3, 4, 5):
            lk = run(k * a, k * c)
            d = abs(lk - l0)
            ratio = d / max(1.0, math.log(a))
            if ratio > worst[k][0]:
                worst[k] = (ratio, d, l0, lk)
    print(f"bits={bits} samples={samples}")
    for k in (2, 3, 4, 5):
        r, d, l0, lk = worst[k]
        print(f"  x{k}: max|dL|={d}  L={l0}->{lk}  max ratio to ln(a)={r:.3f}", flush=True)
    print()
