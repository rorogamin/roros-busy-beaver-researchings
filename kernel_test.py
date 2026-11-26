import sys

def chain_len(c):
    a = 1
    n = 0
    while True:
        n += 1
        if a <= c:
            if a % 2 == 0:
                if c % 2 == 0:
                    return n
                a, c = 1, a // 2 + c + 2
            elif c % 2 == 0:
                a, c = 3 * a, c - a + 4
            else:
                a, c = 3 * a + 2, c - a + 1
        else:
            r = c % 4
            if r in (0, 2):
                a, c = a - c - 1, 3 * (c // 2) + 2
            elif r == 1:
                if a == c + 1:
                    return n
                a, c = a - c - 2, 3 * (c // 2) + 5
            elif a == c + 1:
                return n
            elif a == c + 2:
                a, c = 3 * c + 8, 1
            elif a == c + 3:
                return n
            else:
                a, c = a - c - 4, 3 * (c // 2) + 8
        if a == 1:
            return n

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
M = 400
L = [0] * (N + 1)
for c in range(1, N + 1):
    L[c] = chain_len(c)

for k in (2, 3, 6, 12):
    print(f"base {k}")
    e = 0
    p = 1
    while p * M <= N and e <= 5:
        sigs = {}
        count = 0
        for r in range(p):
            # signature on n=1..M where index in range
            sig = tuple(L[p * n + r] if p * n + r <= N else -1 for n in range(1, M + 1))
            if sig not in sigs:
                sigs[sig] = 0
                count += 1
        print(f"  e={e} p={p} subsequences={p} distinct_signatures={count}", flush=True)
        e += 1
        p *= k
