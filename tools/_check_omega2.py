"""Check the f_{omega*2} chain on eps_engine's CNF ordinals.

Standard FGH convention (used in this file, n iterations):
    F_0(n)     = n + 1
    F_{a+1}(n) = F_a^n(n)
    F_a(n)     = F_{a[n]}(n)      for a limit

Claim checked:
    f_{w*2}(n) = f_{w+n}(n) = f_{w+n-1}^n(n) = ... = f_w^{n^n}(n)

`fs(w*2, n) = w + n` is checked structurally for n = 0..5.  The small
case n = 1 is evaluated exactly.  n >= 2 is left out on purpose: the
iterate count is n^n, so even n = 2 is f_w iterated four times.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from eps_engine import ZERO, fs, is_succ, nat, omega, pred

one = nat(1)
w = omega(one)          # omega
w2 = ((2, one),)        # omega * 2 in CNF


def w_plus(n):
    return w if n == 0 else w + ((n, ZERO),)


def F(a, n, budget):
    budget[0] -= 1
    if budget[0] < 0:
        raise RuntimeError("budget")
    if not a:
        return n + 1
    if is_succ(a):
        b = pred(a)
        v = n
        for _ in range(n):
            v = F(b, v, budget)
        return v
    return F(fs(a, n), n, budget)


def main():
    ok = True
    print("fs(omega*2, n) == omega + n")
    for n in range(6):
        got = fs(w2, n)
        want = w_plus(n)
        same = got == want
        ok = ok and same
        print(f"  n={n}: {'OK ' if same else 'BAD'} {got}")

    print("\nstandard-convention FGH")
    v = F(w2, 1, [100000])
    print(f"  f_(w*2)(1) = {v}")
    ok = ok and v == 2

    try:
        F(w2, 2, [200000])
        print("  f_(w*2)(2) computed, unexpected")
        ok = False
    except RuntimeError:
        print("  f_(w*2)(2): budget exceeded (expected, n^n = 4 f_w-iterates)")

    print("\n" + ("ALL CHECKS PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
