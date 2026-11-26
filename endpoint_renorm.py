import random, math

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

def F(c, cap=200000):
    a = 1
    for _ in range(cap):
        k, a2, c2 = step(a, c)
        if k == 'H':
            return None
        if a2 == 1:
            return c2
        a, c = a2, c2
    return 'CAP'

def report(tag, m, r):
    if m <= 1:
        print(f"{tag}: m={m} r={r} skipped (log 0)")
        return
    fm = F(m)
    f3 = F(3*m + r)
    if fm is None or f3 is None:
        print(f"{tag}: m={m} r={r} F(m)={fm} F(3m+r)={f3}")
        return
    e = f3 - 3*fm
    lm = math.log(m)
    print(f"{tag}: bits={m.bit_length()} r={r} F(m) bits={fm.bit_length()} "
          f"F(3m+r) bits={f3.bit_length()} err={e} e/ln={e/lm:.3f} "
          f"e/bits={e/m.bit_length():.3f}")

print("== known worst ==")
for m, r in ((460381866,0),(3814756888,1),(3814756887,2),(831343756,0),
             (33053026,0),(546567,0),(1,0),(2,0),(3,0),(4,0),(5,0)):
    report("worst", m, r)

print("== random ==")
random.seed(758)
for bits in (32, 64, 128, 256, 463, 700, 1000):
    worst = None
    for _ in range(300 if bits <= 463 else 100):
        m = random.getrandbits(bits) | (1 << (bits-1))
        if m <= 1:
            continue
        for r in (0,1,2):
            fm = F(m); f3 = F(3*m+r)
            if fm is None or f3 is None:
                continue
            ratio = abs(f3 - 3*fm)/math.log(m)
            if worst is None or ratio > worst[0]:
                worst = (ratio, f3 - 3*fm, r, m)
    if worst:
        print(f"bits={bits} worst |e|/ln={worst[0]:.3f} e={worst[1]} r={worst[2]} m={worst[3]}")
