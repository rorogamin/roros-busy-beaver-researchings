"""Ordinals below eps_1, one rung above eps_engine.py.

Why a new layer is needed.  Every ordinal below eps_0 can be written as a
finite CNF term over {0, +, w^}.  eps_0 itself cannot: it is the least fixed
point of w^, so no finite tower names it.  To talk about ordinals *above*
eps_0 (and below eps_1) the notation needs one more symbol, an atom for eps_0,
with the rule

    eps_0[n] = tower of n omegas        (1, w, w^w, w^(w^w), ...)

and the ordinary rules on top of it:

    (b + w^g * k)[n] = b + w^g * (k-1) + w^(g[n])      if g is a limit
    (b + w^(d+1) * k)[n] = b + w^g * (k-1) + w^d * (n+1)

This is the "second feedback" rung in EPSILON_ANALYSIS.md: below eps_0 the
descent engine's parameter is a *number* read off the tape; below eps_1 the
parameter is an *ordinal notation*, whose fundamental sequence is itself a
computation.  A machine at this rung has to re-read its own count field as a
program, twice over.

Representation: a term is a tuple of (exp, coeff) pairs with strictly
decreasing exps; an exp is ('e',) for eps_0 or ('o', term) for a term below it.
All terms without the ('e',) atom are < eps_0, so exponent order only has to
place ('e',) above them.

Checks (run this file): tower heights, eps_0's own sequence, the successor
case, eps_0*k, and that every fs value is strictly below its argument and
non-decreasing in n.
"""

import sys


def zero():
    return ()


def is_zero(a):
    return len(a) == 0


def exp_zero(e):
    return e[0] == 'o' and is_zero(e[1])


def exp_cmp(x, y):
    # ('e',) is eps_0, but ('o', t) may be a term above eps_0 (e.g. eps_0+1),
    # so compare by ordinal value, not by tag.
    if x[0] == 'e' and y[0] == 'e':
        return 0
    if x[0] == 'e':
        return -cmp(y[1], E0)
    if y[0] == 'e':
        return cmp(x[1], E0)
    return cmp(x[1], y[1])


def cmp(a, b):
    """Compare two CNF terms."""
    if is_zero(a):
        return 0 if is_zero(b) else -1
    if is_zero(b):
        return 1
    (ea, ka), (eb, kb) = a[0], b[0]
    c = exp_cmp(ea, eb)
    if c != 0:
        return c
    if ka != kb:
        return -1 if ka < kb else 1
    return cmp(a[1:], b[1:])


def add(a, b):
    """CNF addition: terms of b are absorbed while their exponent is larger."""
    if is_zero(a):
        return b
    if is_zero(b):
        return a
    (ea, ka), (eb, kb) = a[0], b[0]
    c = exp_cmp(ea, eb)
    if c < 0:
        return b
    if c > 0:
        return (a[0],) + add(a[1:], b)
    return ((ea, ka + kb),) + add(a[1:], b[1:])


E0 = (((('e',), 1),))


def norm_exp(g):
    return ('e',) if cmp(g, E0) == 0 else ('o', g)


def omega_pow(e):
    return ((norm_exp(e[1]) if e[0] == 'o' else e, 1),)


def one():
    return omega_pow(('o', zero()))


def nat(n):
    return (((('o', zero()), n),)) if n else zero()


def succ(a):
    return add(a, one())


def mul_omega_pow(e, k):
    return ((norm_exp(e[1]) if e[0] == 'o' else e, k),)


def is_limit(a):
    """Limit iff non-empty and the last exponent is not 0."""
    return bool(a) and not exp_zero(a[-1][0])


def pred(a):
    """Predecessor of a successor term."""
    e, k = a[-1]
    assert exp_zero(e), 'pred of a limit'
    if k == 1:
        return a[:-1]
    return a[:-1] + ((e, k - 1),)


def tower(n):
    """eps_0[n]: n omegas, starting at 1."""
    t = one()
    for _ in range(n):
        t = omega_pow(('o', t))
    return t


def fs(a, n):
    """Fundamental sequence below eps_1; None for 0 and successors."""
    if not a:
        return None
    e, k = a[-1]
    if exp_zero(e):
        return None
    beta = a[:-1]
    if k > 1:
        beta = beta + ((e, k - 1),)
    if e[0] == 'e':
        return add(beta, tower(n))
    g = e[1]
    if is_limit(g):
        return add(beta, omega_pow(('o', fs(g, n))))
    delta = pred(g)
    return add(beta, mul_omega_pow(('o', delta), n + 1))


def show(a):
    if is_zero(a):
        return '0'
    parts = []
    for e, k in a:
        if e[0] == 'e':
            base = 'eps0'
        elif is_zero(e[1]):
            base = '1'
        else:
            base = f'w^{show(e[1])}'
        parts.append(base if k == 1 else f'{base}*{k}')
    return ' + '.join(parts)


def check():
    ok = True

    def eq(name, got, want):
        nonlocal ok
        good = got == want
        ok = ok and good
        print(f'  {name}: {show(got)}  {"==" if good else "!="} {show(want)}')

    def lt(name, a, b):
        nonlocal ok
        good = cmp(a, b) < 0
        ok = ok and good
        print(f'  {name}: {show(a)} < {show(b)}  {"PASS" if good else "FAIL"}')

    print('eps_0[n] is the tower:')
    eq('eps0[0]', fs(E0, 0), one())
    eq('eps0[1]', fs(E0, 1), omega_pow(('o', one())))
    eq('eps0[2]', fs(E0, 2), omega_pow(('o', omega_pow(('o', one())))))
    eq('eps0[3]', fs(E0, 3), omega_pow(('o', omega_pow(('o', omega_pow(('o', one())))))))

    print('eps_0 is a limit, above every finite tower:')
    ok = ok and is_limit(E0)
    lt('eps0[2] < eps0', fs(E0, 2), E0)
    lt('eps0[2] < eps0[3]', fs(E0, 2), fs(E0, 3))
    lt('w^w^w < eps0', omega_pow(('o', omega_pow(('o', omega_pow(('o', one())))))), E0)

    print('eps_0 + 1 is a successor, its fs is not defined:')
    ok = ok and fs(succ(E0), 2) is None

    print('w^(eps_0+1) = eps_0*w:  (eps0*w)[n] = eps0*(n+1)')
    e0w = omega_pow(('o', succ(E0)))
    eq('(eps0*w)[3]', fs(e0w, 3), mul_omega_pow(('e',), 4))

    print('eps_0*2:  (eps0*2)[n] = eps0 + tower(n)')
    e0_2 = add(E0, E0)
    eq('(eps0*2)[2]', fs(e0_2, 2), add(E0, omega_pow(('o', omega_pow(('o', one()))))))

    print('ordering invariants for a handful of terms:')
    samples = [E0, succ(E0), add(E0, E0), omega_pow(('o', succ(E0))),
               add(omega_pow(('o', succ(E0))), omega_pow(('o', one())))]
    for a in samples:
        if fs(a, 0) is None:
            print(f'  {show(a)}: successor, skipped')
            continue
        for n in range(3):
            lt(f'{show(a)}[{n}] < arg', fs(a, n), a)
            good = cmp(fs(a, n), fs(a, n + 1)) <= 0
            ok = ok and good
            print(f'  {show(a)}[{n}] <= {show(a)}[{n+1}]: {"PASS" if good else "FAIL"}')
    return ok



def F_step(a, n):
    """One unfolding of the fast-growing hierarchy at a limit: F_a(n) = F_{a[n]}(n).

    Returns a[n], or None where the hierarchy needs the successor clause
    (F_{b+1}(n) = F_b iterated n+1 times, which is not a single step).
    """
    return fs(a, n) if is_limit(a) else None


def check_f():
    ok = True
    got = F_step(E0, 3)
    good = got == tower(3)
    ok = ok and good
    print(f'  F_eps0(3) unfolds to F_(eps0[3])(3): {show(got)} '
          f'{"== tower(3)" if good else "!= tower(3)"} {"PASS" if good else "FAIL"}')
    good = F_step(succ(E0), 2) is None
    ok = ok and good
    print(f'  F_(eps0+1)(2) needs the successor clause: {"PASS" if good else "FAIL"}')
    got = F_step(omega_pow(('o', succ(E0))), 2)
    good = got == mul_omega_pow(('e',), 3)
    ok = ok and good
    print(f'  F_(eps0*w)(2) unfolds to F_(eps0*3)(2): {show(got)} '
          f'{"PASS" if good else "FAIL"}')
    return ok

if __name__ == '__main__':
    ok = check()
    print('F hierarchy:')
    ok = check_f() and ok
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
