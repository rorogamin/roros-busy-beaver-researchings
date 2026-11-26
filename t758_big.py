"""Big-integer sampler for the post-j family  a_0 = 2*3^k - 1,  1 <= c_0 < 2*3^k.

Exact ten-rule step function of M_758_TBudget.lean / BB33_758_TBudget.v.
Reports the halting time T, the phase structure (maximal L/J runs), and the
per-phase lengths, so the growth of the extremal run with k can be measured.
"""
import sys
import random
from collections import Counter


def rule(a, c):
    if a <= c:
        if a % 2 == 0:
            return 'halt' if c % 2 == 0 else 'h'
        return 'i' if c % 2 == 0 else 'j'
    r = c % 4
    if r in (0, 2):
        return 'a'
    if r == 1:
        return 'halt' if a == c + 1 else 'b'
    if a == c + 1 or a == c + 3:
        return 'halt'
    if a == c + 2:
        return 'e'
    return 'c'


def step(a, c):
    """returns (a', c', halted)"""
    r = rule(a, c)
    if r == 'halt':
        return a, c, True
    if r == 'h':
        return 1, a // 2 + c + 2, False
    if r == 'i':
        return 3 * a, c - a + 4, False
    if r == 'j':
        return 3 * a + 2, c - a + 1, False
    if r == 'a':
        return a - c - 1, 3 * (c // 2) + 2, False
    if r == 'b':
        return a - c - 2, 3 * ((c - 1) // 2) + 5, False
    if r == 'e':
        return 3 * c + 8, 1, False
    if r == 'c':
        return a - c - 4, 3 * ((c - 1) // 2) + 8, False
    raise AssertionError(r)


LEFT = frozenset('abce')


def run(a, c, cap=400000):
    """returns (T, halted, phases) where phases = list of (side, len)"""
    phases = []
    cur = None
    ln = 0
    T = 0
    while True:
        r = rule(a, c)
        if r == 'halt':
            if cur is not None:
                phases.append((cur, ln))
            return T + 1, True, phases
        side = 'L' if r in LEFT else 'J'
        if side != cur:
            if cur is not None:
                phases.append((cur, ln))
            cur, ln = side, 0
        a, c, _ = step(a, c)
        T += 1
        ln += 1
        if T > cap:
            phases.append((cur, ln))
            return T, False, phases


def fam(k, c):
    return 2 * 3 ** k - 1, c


def main():
    mode = sys.argv[1]

    if mode == 'one':
        k, c = int(sys.argv[2]), int(sys.argv[3])
        T, h, ph = run(*fam(k, c))
        print(f'k={k} c={c} T={T} halted={h} phases={len(ph)}')
        for i, (s, n) in enumerate(ph):
            print(f'  {i:3d} {s} {n:5d}')
        return

    if mode == 'scan':
        # exhaustive small windows / ranges, big-int safe
        k = int(sys.argv[2])
        lo, hi = int(sys.argv[3]), int(sys.argv[4])
        bestT = (-1, None)
        bestP = (-1, None)
        hist = Counter()
        for c in range(lo, hi + 1):
            T, h, ph = run(*fam(k, c))
            if T > bestT[0]:
                bestT = (T, c)
            if len(ph) > bestP[0]:
                bestP = (len(ph), c)
            hist[len(ph)] += 1
        print(f'k={k} c in [{lo},{hi}]  maxT={bestT}  maxPhases={bestP}')
        print('  phase histogram:', dict(sorted(hist.items())))
        return

    if mode == 'rand':
        k = int(sys.argv[2])
        n = int(sys.argv[3])
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        rng = random.Random(seed)
        hi = 2 * 3 ** k - 1
        bestT = (-1, None)
        bestP = (-1, None)
        tot = 0
        for _ in range(n):
            c = rng.randrange(1, hi + 1)
            T, h, ph = run(*fam(k, c))
            tot += T
            if T > bestT[0]:
                bestT = (T, c)
            if len(ph) > bestP[0]:
                bestP = (len(ph), c)
        print(f'k={k} random n={n}  meanT={tot / n:.1f}  maxT={bestT}  maxPhases={bestP}')
        return

    raise SystemExit('unknown mode')


if __name__ == '__main__':
    main()
