"""Wide exhaustive window at k = 292 for the halving run of holdout #758.

Tests every c in [1, WINDOW] (a wide contiguous window, not a sample), the
near-cancellation grid c = round(A/m) for m <= MMAX, and RAND uniform draws.
Records T and dQ = Q_end - Q_0; HBudget 30000 is dQ <= 30000.
"""
from multiprocessing import Pool
import random

k = 292
A = 2 * 3 ** k - 1
WINDOW = 1200000
MMAX = 20000
RAND = 200000


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
    cs = list(range(1, WINDOW + 1))
    for m in range(2, MMAX + 1):
        v = (A + m // 2) // m
        if 1 <= v < A:
            cs.append(v)
    rng = random.Random(292292)
    cs += [rng.randrange(1, A) for _ in range(RAND)]
    cs = sorted(set(cs))
    print("k=292 wide window: %d values" % len(cs), flush=True)
    bestT = (-1, 0)
    bestQ = (-1, 0)
    with Pool() as pool:
        for idx, (t, dq, c0) in enumerate(pool.imap_unordered(run, cs, chunksize=512)):
            if dq < 0:
                print("CAP EXCEEDED at c=%d" % c0, flush=True)
            if t > bestT[0]:
                bestT = (t, c0)
            if dq > bestQ[0]:
                bestQ = (dq, c0)
            if idx and idx % 200000 == 0:
                print("  %d/%d  maxT=%d  maxdQ=%d" % (idx, len(cs), bestT[0], bestQ[0]), flush=True)
    print("FINAL maxT=%d at c=%d   maxdQ=%d at c=%d" % (bestT[0], bestT[1], bestQ[0], bestQ[1]))
    print("HBudget 30000 at k=292: %s" % ("HOLDS (maxdQ=%d, margin %.2fx)" % (bestQ[0], 30000.0 / max(bestQ[0], 1)) if bestQ[0] <= 30000 else "FAILS"))


if __name__ == "__main__":
    main()
