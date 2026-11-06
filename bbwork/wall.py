"""Extend the known exploding stretch of BB(3,3) holdout 758.

For c near H = (3^307 - 8282708212)/13959275, the documented A(a,c) chain
map is iterated from A(1,c) until it returns to A(1,c') or halts.  The wiki
states that every c in [H-8_000_000, H-3_403_055] reaches H, but the lower
end of that stretch is not known.  This script tests consecutive c values
immediately below H-8_000_000 and reports how far the stretch continues.

The rules are validated separately against all 26 published halting values
below 10^6 (see delta.c / halts1m.txt).
"""
import sys
import time


def step(a, c):
    """One A(a,c) rule. Returns (a, c, halt, label)."""
    if c + 1 <= a and c % 2 == 0:                       # (a)
        return a - c - 1, 3 * (c // 2) + 2, False, 'a'
    if c + 2 <= a and c % 4 == 1:                       # (b)
        return a - c - 2, 3 * ((c - 1) // 2) + 5, False, 'b'
    if c + 4 <= a and c % 4 == 3:                       # (c)
        return a - c - 4, 3 * ((c - 1) // 2) + 8, False, 'c'
    if c + 3 == a and c % 4 == 3:                       # (d)
        return a, c, True, 'd'
    if c + 2 == a and c % 4 == 3:                       # (e)
        return 3 * c + 8, 1, False, 'e'
    if c + 1 == a and c % 2 == 1:                       # (f)
        return a, c, True, 'f'
    if c >= a and a % 2 == 0 and c % 2 == 0:            # (g)
        return a, c, True, 'g'
    if c >= a and a % 2 == 0 and c % 2 == 1:            # (h)
        return 1, a // 2 + c + 2, False, 'h'
    if c >= a and a % 2 == 1 and c % 2 == 0:            # (i)
        return 3 * a, c - a + 4, False, 'i'
    if c >= a and a % 2 == 1 and c % 2 == 1:            # (j)
        return 3 * a + 2, c - a + 1, False, 'j'
    raise RuntimeError(f"no rule for A({a},{c})")


def chain(c0, trace=False):
    a, c = 1, c0
    n = 0
    path = []
    while True:
        a, c, halt, lab = step(a, c)
        n += 1
        if trace:
            path.append(lab)
        if halt:
            return ('halt', a, c, n, ''.join(path))
        if a == 1:
            return ('end', a, c, n, ''.join(path))
        if n > 10_000_000:
            raise RuntimeError(f"chain guard at {c0}")


H = (3 ** 307 - 8282708212) // 13959275
LOW = H - 8_000_000
HIGH = H - 3_403_055

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    # sanity checks
    assert chain(12)[0] == 'halt'
    r3 = chain(3)
    assert r3[0] == 'end' and r3[2] == 23, r3
    print(f"H has {len(str(H))} digits")
    print(f"known stretch [{LOW}, {HIGH}] length {HIGH-LOW+1}")
    t0 = time.time()
    good = 0
    first_bad = None
    for k in range(1, n + 1):
        c = LOW - k
        kind, a, c2, steps, path = chain(c)
        if kind == 'end' and c2 == H:
            good += 1
        else:
            first_bad = (k, c, kind, a, c2, steps, path)
            break
    dt = time.time() - t0
    print(f"tested {good + (1 if first_bad else 0)} values below LOW in {dt:.2f}s")
    if first_bad:
        k, c, kind, a, c2, steps, path = first_bad
        print(f"first failure at k={k} c=H-{8_000_000+k}: {kind} "
              f"steps={steps} c'=H-{H-c2 if kind!='halt' else 'n/a'}")
        print(f"path={path}")
        print(f"=> wall extends to H-{8_000_000 + k - 1} (lower bound)")
    else:
        print(f"all {good} reach H => wall extends to H-{8_000_000 + good}")
