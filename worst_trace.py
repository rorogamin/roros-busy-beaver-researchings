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

def trace(c0, cap=100000):
    a, c = 1, c0
    out = []
    for n in range(cap):
        kind, a2, c2 = step(a, c)
        out.append((kind, a, c))
        if kind == 'Halt':
            return out, 'halt', None
        a, c = a2, c2
        if a == 1:
            out.append(('end', a, c))
            return out, 'return', c
    return out, 'guard', None

def common_prefix(w1, w2):
    n = min(len(w1), len(w2))
    i = 0
    while i < n and w1[i][0] == w2[i][0]:
        i += 1
    return i

def analyze(m, r):
    w1, e1, F1 = trace(m)
    w3, e3, F3 = trace(3*m + r)
    cp = common_prefix(w3, w1)
    print(f"m={m} r={r} L(m)={len(w1)} L(3m+r)={len(w3)} defect={len(w3)-len(w1)} exits={e1}/{e3}")
    print(f"  common prefix of rule labels: {cp}")
    for name, w, i in (("m", w1, cp), ("3m+r", w3, cp)):
        print(f"  {name} around divergence:")
        for j in range(max(0, i-3), min(len(w), i+8)):
            k, a, c = w[j]
            print(f"    {j:3d} {k} ({a},{c})")
    print()

for m, r in ((460381866,0), (3814756888,1), (3814756887,2), (831343756,0), (33053026,0), (546567,0)):
    analyze(m, r)
