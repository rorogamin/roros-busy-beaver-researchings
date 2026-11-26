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

def jrun(c):
    a = 1
    k = 0
    while True:
        kind, a2, c2 = step(a, c)
        if kind != 'j':
            return k, a, c
        a, c = a2, c2
        k += 1

def trace(a, c, cap=1000):
    out = []
    for _ in range(cap):
        kind, a2, c2 = step(a, c)
        out.append((kind, a, c))
        if kind == 'Halt':
            return out, 'Halt'
        a, c = a2, c2
        if a == 1:
            out.append(('end', a, c))
            return out, 'return'
    return out, 'guard'

for m in (33, 100, 1000, 12345):
    k, a1, c1 = jrun(m)
    _, a2, c2 = jrun(3*m)
    # aligned states: (a2,c2) and (3a1,3c1) differ by (2,-4k)
    t1, e1 = trace(a2, c2)
    t2, e2 = trace(3*a1, 3*c1)
    print(f"m={m} k={k} 3m={3*m} jruns: m->({a1},{c1}) 3m->({a2},{c2})")
    print(f"  lengths: {len(t1)}({e1}) vs {len(t2)}({e2})  diff={len(t1)-len(t2)}")
    n = min(len(t1), len(t2))
    for i in range(n):
        k1, A1, C1 = t1[i]
        k2, A2, C2 = t2[i]
        mark = ' ' if k1 == k2 else '*'
        if i < 12 or i > n-12 or k1 != k2:
            print(f"  {i:3d} {mark} {k1} ({A1},{C1})   {k2} ({A2},{C2})   dA={A1-A2} dC={C1-C2}")
    print()
