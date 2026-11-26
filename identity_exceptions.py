"""identity_exceptions.py -- where does L(3m+r) = L(m)+1 fail?

scale3_exact.c reports the defect is nonzero for a few percent of m.  This
prints the first exceptions and their chains, so the failure mechanism (the
mod-4 branch crossing) can be read off directly.

usage: python identity_exceptions.py [N]
"""
import sys


def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return None
            return (1, a // 2 + c + 2)
        if c % 2 == 0:
            return (3 * a, c - a + 4)
        return (3 * a + 2, c - a + 1)
    r = c % 4
    if r in (0, 2):
        return (a - c - 1, 3 * (c // 2) + 2)
    if r == 1:
        if a == c + 1:
            return None
        return (a - c - 2, 3 * (c // 2) + 5)
    if a == c + 1:
        return None
    if a == c + 2:
        return (3 * c + 8, 1)
    if a == c + 3:
        return None
    return (a - c - 4, 3 * (c // 2) + 8)


def run(c0, trace=False, cap=100000):
    a, c = 1, c0
    tr = [(a, c)]
    for n in range(1, cap + 1):
        nxt = step(a, c)
        if nxt is None:
            return (n, tr if trace else None)
        a, c = nxt
        tr.append((a, c))
        if a == 1:
            return (n, tr if trace else None)
    return (-1, tr if trace else None)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    # sanity: the published small halting values
    for c in (12, 14):
        n, _ = run(c)
        print(f"  L({c}) = {n} (chain length; published TM halts at 5153/5193 TM steps)")
    worst = [0, 0, 0]
    arg = [0, 0, 0]
    exc = {0: [], 1: [], 2: []}
    for m in range(1, N + 1):
        lm, _ = run(m)
        for r in (0, 1, 2):
            l3, _ = run(3 * m + r)
            d = abs(l3 - lm - (1 if r != 1 else 1))
            if d > worst[r]:
                worst[r], arg[r] = d, m
            if d > 0 and len(exc[r]) < 4:
                exc[r].append((m, lm, l3, d))
    print(f"scanned m <= {N}")
    for r in (0, 1, 2):
        print(f"  r={r}: max |L(3m+r)-L(m)-1| = {worst[r]} at m={arg[r]}")
        for e in exc[r]:
            print(f"      m={e[0]} L(m)={e[1]} L(3m+r)={e[2]} defect={e[3]}")
    # trace the smallest r=0 exception
    if exc[0]:
        m = exc[0][0][0]
        _, t1 = run(m, trace=True)
        _, t3 = run(3 * m, trace=True)
        print(f"  trace m={m} (len {len(t1)}) vs 3m={3*m} (len {len(t3)})")
        n = max(len(t1), len(t3))
        for i in range(n):
            s1 = t1[i] if i < len(t1) else None
            s3 = t3[i] if i < len(t3) else None
            mark = "" if s1 != s3 else "  =="
            if i < 12 or i > n - 8 or s1 != s3:
                print(f"    {i:3d}  m:{s1}   3m:{s3}{mark}")


if __name__ == "__main__":
    main()
