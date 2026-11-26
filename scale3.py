import random

def chain_trace(c, cap=200000):
    a = 1
    n = 0
    word = []
    while True:
        n += 1
        if n > cap:
            return n, 'guard', word, None
        if a <= c:
            if a % 2 == 0:
                if c % 2 == 0:
                    return n, 'halt', word, None
                word.append('h')
                a, c = 1, a // 2 + c + 2
            elif c % 2 == 0:
                word.append('i')
                a, c = 3 * a, c - a + 4
            else:
                word.append('j')
                a, c = 3 * a + 2, c - a + 1
        else:
            if c % 4 in (0, 2):
                word.append('a')
                a, c = a - c - 1, 3 * (c // 2) + 2
            elif c % 4 == 1:
                if a == c + 1:
                    return n, 'halt', word, None
                word.append('b')
                a, c = a - c - 2, 3 * (c // 2) + 5
            elif a == c + 1:
                return n, 'halt', word, None
            elif a == c + 2:
                word.append('e')
                a, c = 3 * c + 8, 1
            elif a == c + 3:
                return n, 'halt', word, None
            else:
                word.append('c')
                a, c = a - c - 4, 3 * (c // 2) + 8
        if a == 1:
            return n, 'return', word, c

def len_only(c):
    n, kind, _, _ = chain_trace(c)
    return n, kind

random.seed(758)
for bits in (64, 128, 256, 463, 700, 1000):
    samples = 4000 if bits <= 256 else 1500
    mx = -10**9; mn = 10**9; arg = None
    diff_hist = {}
    for _ in range(samples):
        c = random.getrandbits(bits) | (1 << (bits - 1))
        lc, kc = len_only(c)
        l3, k3 = len_only(c // 3)
        d = lc - l3
        diff_hist[d] = diff_hist.get(d, 0) + 1
        if d > mx: mx, arg = d, (c, lc, l3, kc, k3)
        if d < mn: mn = d
    print(f"bits={bits} samples={samples} max(L(c)-L(c/3))={mx} min={mn} arg={arg}", flush=True)
    print("  hist top:", sorted(diff_hist.items(), key=lambda kv: -kv[1])[:8], flush=True)
