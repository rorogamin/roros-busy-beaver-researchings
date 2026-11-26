import random, math, sys

def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return 'H', a, c
            return 'h', 1, a // 2 + c + 2
        if c % 2 == 0:
            return 'i', 3 * a, c - a + 4
        return 'j', 3 * a + 2, c - a + 1
    r = c % 4
    if r in (0, 2):
        return 'a', a - c - 1, 3 * (c // 2) + 2
    if r == 1:
        if a == c + 1:
            return 'H', a, c
        return 'b', a - c - 2, 3 * (c // 2) + 5
    if a == c + 1:
        return 'H', a, c
    if a == c + 2:
        return 'e', 3 * c + 8, 1
    if a == c + 3:
        return 'H', a, c
    return 'c', a - c - 4, 3 * (c // 2) + 8

def L(c, cap=200000):
    a = 1
    n = 0
    while True:
        n += 1
        if n > cap: return n
        k, a, c = step(a, c)
        if k == 'H': return n
        if a == 1: return n

def defect(m, r):
    return L(3*m + r) - L(m)

def report(tag, m, r=0):
    d = defect(m, r)
    lm = math.log(m) if m > 1 else 1.0
    print(f"{tag}: m bits={m.bit_length()} r={r} L(m)={L(m)} L(3m+r)={L(3*m+r)} defect={d} d/ln={d/lm:.3f}")

random.seed(758)
print("== random huge ==")
for bits in (128, 256, 463, 700, 1000, 2000, 5000, 10000):
    samples = 300 if bits <= 1000 else (50 if bits <= 5000 else 20)
    worst = None
    for _ in range(samples):
        m = random.getrandbits(bits) | (1 << (bits - 1))
        for r in (0, 1, 2):
            d = defect(m, r)
            ratio = abs(d) / math.log(m)
            if worst is None or ratio > worst[0]:
                worst = (ratio, d, r, m)
    print(f"bits={bits} samples={samples} worst |d|/ln={worst[0]:.3f} d={worst[1]} r={worst[2]}", flush=True)

print("== scaled known worst ==")
base = [(460381866,0), (3814756888,1), (3814756887,2), (831343756,0), (33053026,0), (546567,0)]
for m0, r in base:
    for e in range(0, 40, 4):
        m = m0 * (3**e)
        report(f"3^{e}*{m0}", m, r)

print("== adversarial hill climb (maximize |defect|/ln m) ==")
for bits in (128, 256, 512, 1024):
    best = None
    for restart in range(40):
        m = random.getrandbits(bits) | (1 << (bits - 1))
        d = max(abs(defect(m, r)) for r in (0,1,2))
        score = d / math.log(m)
        for it in range(200):
            # mutate 1-3 bits
            m2 = m
            for _ in range(random.randint(1, 3)):
                b = random.randrange(bits)
                m2 ^= 1 << b
            if m2 < 1: continue
            d2 = max(abs(defect(m2, r)) for r in (0,1,2))
            s2 = d2 / math.log(m2)
            if s2 > score:
                m, d, score = m2, d2, s2
        if best is None or score > best[0]:
            best = (score, d, m)
    print(f"bits={bits} best |d|/ln={best[0]:.3f} d={best[1]} m={best[2]}", flush=True)
