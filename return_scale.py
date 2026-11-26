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

def chain(c0, cap=200000):
    a, c = 1, c0
    n = 0
    while True:
        n += 1
        if n > cap: return n, 'guard', None
        kind, a, c = step(a, c)
        if kind == 'Halt': return n, 'halt', None
        if a == 1: return n, 'return', c

random.seed(758)
for bits in (64, 128, 256, 463, 700, 1000):
    samples = 3000 if bits <= 256 else 1000
    worst = None
    for _ in range(samples):
        m = random.getrandbits(bits) | (1 << (bits - 1))
        lm, km, Fm = chain(m)
        l3, k3, F3 = chain(3 * m)
        if Fm is None or F3 is None:
            continue
        err = abs(F3 - 3 * Fm)
        ratio = err / max(1, bits)
        if worst is None or ratio > worst[0]:
            worst = (ratio, m, lm, l3, Fm, F3, err)
    print(f"bits={bits} samples={samples} worst err/bits={worst[0]:.3f} err={worst[6]} "
          f"L(m)={worst[2]} L(3m)={worst[3]}", flush=True)
