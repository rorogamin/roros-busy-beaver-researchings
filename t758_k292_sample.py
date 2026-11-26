"""Wide structured sample of the halving run near k = 292 for holdout #758.

Halving rule: stop on a true halt, on a' = 1, or on 2*c' <= c0.
For each c we record the halving time T and the growth dQ = Q_end - Q_0 of
Q = a + 2c, which is what HBudget bounds.

Sample families (k = 292, A = 2*3^292 - 1):
  * small:        c in [1, SMALL]
  * extremal:     c in [2047 - NEAR, 2047 + NEAR]   (2047 is the known extremal)
  * structured:   c = round(A / m) for m = 2 .. MMAX  (near-cancellation values)
  * pgrid:        c = round(A * 2^-i * 3^-j) on a coarse grid
  * random:       RAND uniform draws from [1, A)
"""
import sys, random
from multiprocessing import Pool

k = 292
A = 2 * 3 ** k - 1
SMALL = 60000
NEAR = 6000
MMAX = 4000
RAND = 20000


def step(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return None
            return (1, a // 2 + c + 2)
        if c % 2 == 0:
            return (3 * a, c - a + 4)
        return (3 * a + 2, c - a + 1)
    m = c % 4
    if m in (0, 2):
        return (a - c - 1, 3 * (c // 2) + 2)
    if m == 1:
        if a == c + 1:
            return None
        return (a - c - 2, 3 * ((c - 1) // 2) + 5)
    if a in (c + 1, c + 3):
        return None
    if a == c + 2:
        return (3 * c + 8, 1)
    return (a - c - 4, 3 * ((c - 1) // 2) + 8)


def run(c0):
    a, c = A, c0
    Q0 = A + 2 * c0
    t = 0
    while True:
        r = step(a, c)
        if r is None:
            t += 1
            break
        a, c = r
        t += 1
        if a == 1 or 2 * c <= c0:
            break
        if t > 100000:
            return (t, -1, c0)
    return (t, a + 2 * c - Q0, c0)


def main():
    cs = []
    cs += list(range(1, SMALL + 1))
    cs += list(range(max(1, 2047 - NEAR), 2047 + NEAR + 1))
    for m in range(2, MMAX + 1):
        v = (A + m // 2) // m
        if 1 <= v < A:
            cs.append(v)
    for i in range(0, 60):
        for j in range(0, 12):
            num, den = A, 1
            den *= 2 ** i
            den *= 3 ** j
            v = (A + den // 2) // den
            if 1 <= v < A:
                cs.append(v)
    rng = random.Random(758758)
    cs += [rng.randrange(1, A) for _ in range(RAND)]
    cs = sorted(set(cs))
    print("samples: %d" % len(cs), flush=True)
    bestT = (-1, 0)
    bestQ = (-1, 0)
    with Pool() as pool:
        for idx, (t, dq, c0) in enumerate(pool.imap_unordered(run, cs, chunksize=256)):
            if dq < 0:
                print("CAP EXCEEDED at c=%d" % c0, flush=True)
            if t > bestT[0]:
                bestT = (t, c0)
            if dq > bestQ[0]:
                bestQ = (dq, c0)
            if idx % 20000 == 0:
                print("  %d/%d  maxT=%d  maxdQ=%d" % (idx, len(cs), bestT[0], bestQ[0]), flush=True)
    print("FINAL  maxT=%d at c=%d   maxdQ=%d at c=%d" % (bestT[0], bestT[1], bestQ[0], bestQ[1]))
    print("HBudget 30000 at k=292: %s" % ("HOLDS (maxdQ=%d)" % bestQ[0] if bestQ[0] <= 30000 else "FAILS"))


if __name__ == "__main__":
    main()
