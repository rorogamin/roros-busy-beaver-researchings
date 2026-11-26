import random, sys

def chain_len(c):
    a = 1
    n = 0
    while True:
        n += 1
        if a <= c:
            if a % 2 == 0:
                if c % 2 == 0:
                    return n, 'halt', None
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
                    return n, 'halt', None
                a, c = a - c - 2, 3 * (c // 2) + 5
            elif a == c + 1:
                return n, 'halt', None
            elif a == c + 2:
                a, c = 3 * c + 8, 1
            elif a == c + 3:
                return n, 'halt', None
            else:
                a, c = a - c - 4, 3 * (c // 2) + 8
        if a == 1:
            return n, 'return', c
        if n > 100000:
            return n, 'guard', None

random.seed(1)
N = 2_000_000
maxd3 = -10**9; arg3 = None
maxd2 = -10**9; arg2 = None
maxd9 = -10**9; arg9 = None
for _ in range(200000):
    c = random.randrange(2, N)
    lc, _, _ = chain_len(c)
    l3, _, _ = chain_len(c // 3) if c >= 3 else (0, 0, 0)
    l2, _, _ = chain_len(c // 2) if c >= 2 else (0, 0, 0)
    l9, _, _ = chain_len(c // 9) if c >= 9 else (0, 0, 0)
    if lc - l3 > maxd3: maxd3, arg3 = lc - l3, (c, lc, l3)
    if lc - l2 > maxd2: maxd2, arg2 = lc - l2, (c, lc, l2)
    if lc - l9 > maxd9: maxd9, arg9 = lc - l9, (c, lc, l9)
print('max L(c)-L(c/3):', maxd3, 'at', arg3)
print('max L(c)-L(c/2):', maxd2, 'at', arg2)
print('max L(c)-L(c/9):', maxd9, 'at', arg9)
