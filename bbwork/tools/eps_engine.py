"""Our own epsilon-zero engine: CNF ordinals below eps_0, fundamental sequences,
and the fast-growing hierarchy F_alpha(n).

This is the "descent engine" that EPSILON_ANALYSIS.md says the repo was missing:
it is what lets a *machine* claim be stated at a rung, instead of only measured.
It is deliberately independent of any Turing machine -- the machines come later.

Representation
    an ordinal is a tuple of (coeff, exponent) pairs, exponents themselves
    ordinals, sorted strictly decreasing:
        ()                      = 0
        ((1, ()),)              = 1
        ((1, ((1, ()),)),)      = omega
        ((1, ((1, ((1,())),)),))= omega^omega
    so epsilon_0 itself is not representable; its fundamental sequences are, and
    eps_0[n] is produced directly by `fs_eps0(n)`.

Hierarchy
    F_0(n)     = n + 1
    F_{a+1}(n) = F_a iterated n+1 times on n
    F_a(n)     = F_{a[n]}(n)          for limit a
"""

import sys

sys.setrecursionlimit(100000)

ZERO = ()


def is_zero(a):
    return a == ZERO


def is_succ(a):
    """a = b + 1  <=>  the last term has exponent 0."""
    return bool(a) and a[-1][1] == ZERO


def pred(a):
    assert is_succ(a)
    c, e = a[-1]
    rest = a[:-1]
    return rest if c == 1 else rest + ((c - 1, e),)


def succ(a):
    if a and a[-1][1] == ZERO:
        c, e = a[-1]
        return a[:-1] + ((c + 1, e),)
    return a + ((1, ZERO),)


def lt(a, b):
    """CNF comparison: leading exponent decides, then coefficient, then tail."""
    if not b:
        return False
    if not a:
        return True
    ca, ea = a[0]
    cb, eb = b[0]
    if ea == eb:
        if ca != cb:
            return ca < cb
        return lt(a[1:], b[1:])
    return lt(ea, eb)


def le(a, b):
    return a == b or lt(a, b)


def add1_term(c, e):
    return ((c, e),) if c else ()


def fs(a, n):
    """a[n] for a limit ordinal a (standard CNF fundamental sequences)."""
    assert a and not is_succ(a), 'fs of a successor'
    c, e = a[-1]
    rest = a[:-1]
    if is_succ(e):                       # omega^(e'+1)*c  ->  omega^e*(c-1) + omega^e'*n
        e0 = pred(e)
        return rest + add1_term(c - 1, e) + add1_term(n, e0)
    # e is a limit: omega^e*c -> omega^e*(c-1) + omega^(e[n])
    return rest + add1_term(c - 1, e) + ((1, fs(e, n)),)


def omega(e):
    return ((1, e),)


def nat(n):
    return () if n == 0 else ((n, ZERO),)


def fs_eps0(n):
    """eps_0[n] = tower of omega of height n  (eps_0[0] = 1 by convention)."""
    a = nat(1)
    for _ in range(n):
        a = omega(a)
    return a


class Budget(Exception):
    pass


def F(a, n, steps=None):
    """F_a(n).  `steps` caps the recursion so huge calls fail fast."""
    if steps is None:
        steps = [2_000_000]
    steps[0] -= 1
    if steps[0] < 0:
        raise Budget
    if not a:
        return n + 1
    if is_succ(a):
        b = pred(a)
        v = n
        for _ in range(n + 1):
            v = F(b, v, steps)
        return v
    return F(fs(a, n), n, steps)


def show(a, limit=60):
    """Compact printing: omega^k chains read best in the standard notation."""
    def one(c, e):
        if e == ZERO:
            return str(c)
        if e == nat(1):
            base = 'w'
        else:
            base = f'w^{show(e, limit)}'
        return base if c == 1 else f'{base}*{c}'
    if not a:
        return '0'
    s = '+'.join(one(c, e) for c, e in a)
    return s if len(s) <= limit else s[:limit - 3] + '...'


def demo():
    print('ordinal identities (eps_0[n] = height-n tower of omega):')
    for n in range(5):
        print(f'  eps_0[{n}] = {show(fs_eps0(n), 46)}')

    print('\nfundamental sequences inside omega^omega:')
    w = omega(nat(1))                      # omega = omega^1
    ww = omega(w)
    print(f'  (w^w)[3]   = {show(fs(ww, 3))}')
    print(f'  (w^2+w)[4] = {show(fs(((1, nat(2)), (1, nat(1))), 4))}')

    print('\nhierarchy values (cap on work, not on size):')
    rows = [('0', ZERO), ('1', nat(1)), ('2', nat(2)), ('3', nat(3)),
            ('w', w), ('w*2', ((2, nat(1)),))]
    for name, a in rows:
        vals = []
        for n in range(4):
            try:
                vals.append(str(F(a, n, [200000])))
            except Budget:
                vals.append('>budget')
            except RecursionError:
                vals.append('>depth')
        print(f'  F_{name:<4}(0..3) = ' + ', '.join(vals))

    print('\nwhy eps_0 differs from any tower:')
    for n in (1, 2, 3):
        e = fs_eps0(n)
        print(f'  eps_0[{n}] has height {n} ({show(e, 30)}); '
              f'F_eps_0({n}) = F_(eps_0[{n}])({n})')
    try:
        v = F(fs_eps0(2), 2, [400000])
        print(f'  F_eps_0(2) = {v}')
    except Budget:
        print('  F_eps_0(2) exceeds the work cap (expected: it is F_(w^w)(2))')


if __name__ == '__main__':
    demo()
