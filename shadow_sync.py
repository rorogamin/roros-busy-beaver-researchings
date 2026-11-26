"""shadow_sync.py -- does the 758 chain from 3m synchronize with the chain from m?

The (R) route needs |L(3m+r) - L(m)| <= C ln m.  The proposed mechanism is
shadowing: the post-j states of m and 3m differ by (2, -4k), and the expanding
map should collapse that perturbation, making the two orbits *identical* after
O(log) steps.  If they merge, the length defect is just the step offset at the
merge, which is exactly what (R) bounds.

usage: python shadow_sync.py [bits] [samples]
"""
import random
import sys

HALT = None


def step(a, c):
    """One rule of the published A(a,c) chain map.  Returns (a,c) or HALT."""
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0:
                return HALT
            return (1, a // 2 + c + 2)
        if c % 2 == 0:
            return (3 * a, c - a + 4)
        return (3 * a + 2, c - a + 1)
    r = c % 4
    if r in (0, 2):
        return (a - c - 1, 3 * (c // 2) + 2)
    if r == 1:
        if a == c + 1:
            return HALT
        return (a - c - 2, 3 * (c // 2) + 5)
    if a == c + 1:
        return HALT
    if a == c + 2:
        return (3 * c + 8, 1)
    if a == c + 3:
        return HALT
    return (a - c - 4, 3 * (c // 2) + 8)


def run(c0, cap=100000):
    """Chain from A(1,c0).  Returns (length, list of states)."""
    a, c = 1, c0
    states = [(a, c)]
    for n in range(1, cap + 1):
        nxt = step(a, c)
        if nxt is HALT:
            return n, states
        a, c = nxt
        if a == 1:
            return n, states
        states.append((a, c))
    return -1, states


def main():
    bits = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    random.seed(12345)
    stats = {0: [], 1: [], 2: []}
    merged = {0: 0, 1: 0, 2: 0}
    worst = []
    for _ in range(samples):
        m = random.getrandbits(bits) | (1 << (bits - 1))
        lm, sm = run(m)
        if lm < 0:
            continue
        index = {s: i for i, s in enumerate(sm)}
        for r in (0, 1, 2):
            c3 = 3 * m + r
            l3, s3 = run(c3)
            if l3 < 0:
                continue
            d = l3 - lm
            stats[r].append(d)
            hit = None
            for j, s in enumerate(s3):
                if s in index:
                    hit = (j, index[s])
                    break
            if hit is not None:
                merged[r] += 1
                if j > max((h[0] for h in worst), default=-1):
                    pass
            if len(worst) < 20:
                worst.append((abs(d), m.bit_length(), d, r, hit))
    n = {r: len(stats[r]) for r in stats}
    print(f"samples={samples} bits={bits} usable={n}")
    for r in (0, 1, 2):
        ds = stats[r]
        if not ds:
            continue
        ds_abs = sorted(abs(d) for d in ds)
        mx = ds_abs[-1]
        p99 = ds_abs[int(0.99 * (len(ds_abs) - 1))]
        mean = sum(ds_abs) / len(ds_abs)
        print(
            f"  r={r}: max|dL|={mx} p99={p99} mean={mean:.2f} "
            f"merged={merged[r]}/{len(ds)} ({100.0*merged[r]/len(ds):.1f}%)"
        )
    worst.sort(reverse=True)
    print("worst |dL| cases (|dL|, bits, dL, r, (j,i_merge)):")
    for w in worst[:8]:
        print("   ", w)


if __name__ == "__main__":
    main()
