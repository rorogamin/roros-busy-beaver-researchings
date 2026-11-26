import random, sys

def chain(c):
    a = 1
    n = 0
    while True:
        n += 1
        if a <= c:
            if a % 2 == 0:
                if c % 2 == 0:
                    return ('halt', n, None)
                a, c = 1, a // 2 + c + 2
            elif c % 2 == 0:
                a, c = 3 * a, c - a + 4
            else:
                a, c = 3 * a + 2, c - a + 1
        else:
            if c % 4 in (0, 2):
                a, c = a - c - 1, 3 * (c // 2) + 2
            elif c % 4 == 1:
                if a == c + 1:
                    return ('halt', n, None)
                a, c = a - c - 2, 3 * (c // 2) + 5
            elif a == c + 1:
                return ('halt', n, None)
            elif a == c + 2:
                a, c = 3 * c + 8, 1
            elif a == c + 3:
                return ('halt', n, None)
            else:
                a, c = a - c - 4, 3 * (c // 2) + 8
        if a == 1:
            return ('return', n, c)

random.seed(758)
for bits in (32, 64, 96, 128, 192, 256, 320, 400, 463, 600, 1000):
    samples = 20000 if bits <= 256 else 4000
    best = 0
    best_c = None
    best_kind = None
    halts = 0
    for _ in range(samples):
        c = random.getrandbits(bits) | (1 << (bits - 1))
        kind, n, _ = chain(c)
        if kind == 'halt':
            halts += 1
        if n > best:
            best, best_c, best_kind = n, c, kind
    print(f"bits={bits} samples={samples} halts={halts} max_len={best} kind={best_kind} log3={best/(bits*0.63093+1):.2f}", flush=True)
