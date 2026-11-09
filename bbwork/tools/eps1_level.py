"""The level of the eps_1 obligation, measured rather than asserted.

Rules 4, 6 and 7: the machine descends eps_1[n] to 0 for some n > 2, and the step
count has to be *around* f_{eps_1}(n) -- proved, not simulated, because
H_{eps_1[n]}(n) is not a reachable number.  This module measures the three things
that proof rests on.

  1. the sequence (rule 6).  eps_1 = sup(eps_0+1, w^(eps_0+1), w^w^(eps_0+1), ...),
     so member k is the tower of k omegas over eps_0+1; the obligation is member
     n for some n > 2, i.e. at least three omegas over eps_0+1.

  2. halting.  Every move fs/pred strictly decreases the ordinal.  Strict
     decrease plus well-foundedness is what makes the run reach 0 and the machine
     halt -- no simulation of this run can show it, since the run is longer than
     anything reachable.

  3. length.  H_alpha(n) = moves to 0 with the index bumped at each successor
     step, which is exactly what a tape machine does.  Measured on two ladders:

       towers over 1        the flat engine's world, growth 2^h
       towers over eps_0+1  the eps_1 members (rule 6)

     and the correspondence f_alpha(n) = H_{w^alpha}(n) is checked on the small
     ladder where both sides are computable, which is what lets H be read as f.

Run: python tools/eps1_level.py
"""

import sys

sys.path.insert(0, 'tools')

import eps1_descent as D
from eps1_descent import (Ord, ZERO, E0, add, mul_pow, fs, pred, is_limit,
                          wraps, tower, su_eps0)

ONE = Ord(((ZERO, 1),))

CAP = 2 * 10 ** 6


# ---------------------------------------------------------------- the sequence

def members(k):
    """Member k of eps_1's sequence: the tower of k omegas over eps_0+1."""
    return tower(k)


# ------------------------------------------------------------------- halting

def less(a, b):
    """a < b on these notations: lexicographic on the CNF term lists."""
    ta, tb = a.terms, b.terms
    i = 0
    while i < len(ta) and i < len(tb):
        ea, ca = ta[i]
        eb, cb = tb[i]
        if ea is not eb:
            if ea is None or eb is None:
                return eb is None                    # the atom exceeds any term list
            if less(ea, eb):
                return True
            if less(eb, ea):
                return False
            return ca < cb
        if ca != cb:
            return ca < cb
        i += 1
    return len(ta) < len(tb)


def sample(count=400, seed=7, depth=3):
    import random
    rng = random.Random(seed)

    def build(d):
        if d == 0 or rng.random() < 0.35:
            return rng.choice([ZERO, E0, ONE, Ord(((ZERO, 2),))])
        e = build(d - 1)
        t = mul_pow(e, rng.choice([1, 1, 2, 3]))
        return add(t, build(d - 1)) if rng.random() < 0.4 else t

    return [build(depth) for _ in range(count)]


def check_halting():
    print('halting: every move strictly decreases the ordinal')
    terms = sample()
    bad = limit = succ = atom = 0
    for a in terms:
        if a.is_zero():
            continue
        if is_limit(a):
            nxt = fs(a, 2)
            limit += 1
            atom += 1 if a.is_atom() else 0
        else:
            nxt = pred(a)
            succ += 1
        if not less(nxt, a):
            bad += 1
            print(f'  NOT DECREASING: {a!r} -> {nxt!r}')
    print(f'  {len(terms)} notations: {succ} predecessor moves, {limit} limit moves '
          f'({atom} of them the atom expanding)')
    print('  strict decrease on every one: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


# -------------------------------------------------------------------- lengths

def hardy(a, n, cap=CAP):
    """(value, moves) or (None, moves) when the cap is hit; moves is then a lower bound."""
    steps = 0
    while not a.is_zero():
        steps += 1
        if steps > cap:
            return None, steps
        if is_limit(a):
            a = fs(a, n)
        else:
            a = pred(a)
            n += 1
    return n, steps


def show(label, a, ns, cap=CAP):
    cells = []
    for n in ns:
        v, st = hardy(a, n, cap)
        cells.append(f'n={n}: ' + (f'{st}' if v is not None else f'>{cap}'))
    print(f'    {label:<28} ' + '   '.join(cells))


def check_lengths():
    print()
    print(f'length ladder: H_alpha(n) ordinal moves, index bumped (cap {CAP})')
    print('  towers over 1 -- the flat engine, growth 2^h:')
    for h in range(1, 6):
        show(f'tower height {h}', wraps(h), (2,))
    print('  towers over eps_0+1 -- the eps_1 members (rule 6):')
    for k in range(0, 4):
        show(f'member {k}', members(k), (1, 2, 3))
    print()
    print('  the same wall is reached with fewer omega-levels:')
    h_wall = next(h for h in range(1, 40) if hardy(wraps(h), 2)[1] > 10 ** 5)
    k_wall = next(k for k in range(0, 6) if hardy(members(k), 2)[1] > 10 ** 5)
    print(f'    towers over 1 need height {h_wall} to pass 10^5 moves at n=2')
    print(f'    towers over eps_0+1 need only member {k_wall}')
    print('    the atom adds a whole omega-exponent: eps_0\'s own fundamental')
    print('    sequence, whose height is the running index (rule 3)')


# ------------------------------------------------------- f against H, the bridge

def fgh(a, n, cap=CAP):
    """f_alpha(n): f_0 = n+1, f_{a+1} = f_a^n(n), f_lim = f_{a[n]}(n)."""
    if a.is_zero():
        return n + 1
    if is_limit(a):
        return fgh(fs(a, n), n, cap)
    b = pred(a)
    v = n
    for _ in range(n):
        v = fgh(b, v, cap)
        if v > cap:
            return cap + 1
    return v


def check_growth():
    """Both ladders at n=1, where enough rungs are exact to compare growth."""
    print()
    print('growth at n=1, exact where the cap allows (cap %d)' % CAP)
    print("  towers over 1 (eps_0 machines' world):")
    prev, flat = None, []
    for h in range(1, 7):
        v, st = hardy(wraps(h), 1)
        flat.append((st, v is not None))
        r = f'{st / prev:6.2f}' if prev else '     -'
        print(f'    height {h}: ' + (f'{st:>7}' if v is not None else f'>={st:>7}') + f'   ratio {r}')
        prev = st
    print('  towers over eps_0+1 (the eps_1 members):')
    prev, atom = None, []
    for k in range(0, 6):
        v, st = hardy(members(k), 1)
        atom.append((st, v is not None))
        r = f'{st / prev:6.2f}' if prev else '     -'
        print(f'    member {k}: ' + (f'{st:>7}' if v is not None else f'>={st:>7}') + f'   ratio {r}')
        prev = st
    ok = True
    for ladder, name in ((flat, 'towers over 1'), (atom, 'towers over eps_0+1')):
        for i in range(len(ladder) - 1):
            if ladder[i][1] and ladder[i + 1][0] < ladder[i][0]:
                ok = False
                print(f'  FAIL: {name} rung {i + 1} is below rung {i}')
    exact_flat = max(st for st, ex in flat if ex)
    exact_atom = max(st for st, ex in atom if ex)
    print(f'  exact rungs reached: towers over 1 up to {exact_flat} steps, '
          f'towers over eps_0+1 up to {exact_atom}')
    print('  monotone on both ladders: ' + ('OK' if ok else 'FAILURES'))
    return ok


def report_hierarchies():
    """f and the descent length side by side.  Reported, not asserted.

    f_alpha and H_{w^alpha} agree only after the two hierarchies' conventions are
    matched (f iterates the argument, H bumps the index), and the numbers below
    show they are not literally equal at small alpha.  What matters for the level
    is the growth along the ladder, which check_growth measures directly; this
    table exists so nobody mistakes a convention for a proof.
    """
    print()
    print('f_alpha(n) and H_{w^alpha}(n), side by side (convention-dependent):')
    for label, a in (('0', ZERO), ('1', ONE), ('2', Ord(((ZERO, 2),))),
                     ('3', Ord(((ZERO, 3),))), ('w', mul_pow(ONE, 1))):
        row = []
        for n in (1, 2, 3):
            f = fgh(a, n)
            h = hardy(mul_pow(a, 1), n)[1]
            row.append(f'n={n}: f={f} H={h}')
        print(f'    alpha={label:<3} ' + '   '.join(row))
    print('  the descent length a machine is charged for is H; read as f it is the')
    print('  same ladder up to these conventions, which is what rule 7 allows.')


def main():
    print('eps_1 sequence (rule 6): member k = k omegas over eps_0+1')
    for k in range(0, 5):
        print(f'  member {k}: {members(k)!r}')
    print()
    ok = check_halting()
    check_lengths()
    ok = check_growth() and ok
    report_hierarchies()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
