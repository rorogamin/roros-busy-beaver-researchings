import random

def step(a, c):
    """Return (kind, a', c') with kind in a,b,c,d,e,f,g,h,i,j, or Halt."""
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
    word = []
    for _ in range(cap):
        kind, a, c = step(a, c)
        word.append(kind)
        if kind == 'Halt':
            return 'Halt', word
        if a == 1:
            return 'return', word
    return 'guard', word

def jrun(c):
    a = 1
    k = 0
    while True:
        kind, a2, c2 = step(a, c)
        if kind != 'j':
            return k, a, c
        a, c = a2, c2
        k += 1

def common_prefix(w1, w2):
    n = min(len(w1), len(w2))
    i = 0
    while i < n and w1[i] == w2[i]:
        i += 1
    return i

random.seed(758)
for bits in (64, 128, 256, 463, 700, 1000):
    samples = 2000 if bits <= 256 else 800
    stats = []
    for _ in range(samples):
        m = random.getrandbits(bits) | (1 << (bits - 1))
        c = 3 * m
        # initial j-runs
        k, am, cm = jrun(m)
        k2, ac, cc = jrun(c)
        # scale the m-state by 3 and compare with the c-state
        da = ac - 3 * am
        dc = cc - 3 * cm
        # run the rest of both chains
        km, w1 = run(am, cm)
        kc, w2 = run(ac, cc)
        cp = common_prefix(w1, w2)
        stats.append((abs(da), abs(dc), k2 - k, len(w1), len(w2), cp, abs(len(w1)-len(w2))))
    mx_da = max(s[0] for s in stats)
    mx_dc = max(s[1] for s in stats)
    mx_dk = max(abs(s[2]) for s in stats)
    mx_ld = max(s[6] for s in stats)
    mx_cp = max(s[5] for s in stats)
    avg_cp = sum(s[5] for s in stats) / len(stats)
    # how much of the shorter word is matched on average
    frac = sum(s[5] / min(s[3], s[4]) for s in stats) / len(stats)
    print(f"bits={bits} samples={samples} max|da|={mx_da} max|dc|={mx_dc} max|dk|={mx_dk} "
          f"max_len_diff={mx_ld} max_prefix={mx_cp} avg_prefix={avg_cp:.1f} match_frac={frac:.4f}", flush=True)
    # one example with the largest length difference
    ex = max(stats, key=lambda s: s[6])
    print("  worst:", ex, flush=True)
