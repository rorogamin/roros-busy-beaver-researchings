"""The eps_1 descent, modelled: ordinals below eps_1 and how many steps to 0.

A Turing machine at level eps_1 has to descend notations, not count.  This module
writes down the notations and their fundamental sequences, and counts how many
descent steps it takes to reach 0 -- that count is the number of "ordinal
decrements" the machine must perform, and it is the thing any candidate machine
has to match.

Notation.  An ordinal below eps_1 is written in Cantor normal form

    a = w^e1 * c1 + w^e2 * c2 + ... + w^ek * ck,   e1 > e2 > ... > ek,

with each exponent itself such a term (mutual recursion), so the whole system is
closed below eps_1.  `O()` is zero, `A(e, c)` is a term w^e * c.

The base of the recursion is the atom `E0` standing for `eps_0 + 1`: eps_1 is the
sup of the tower w^w^...^(eps_0 + 1), so a tower of height h reaches the h-th
member of that sequence and the descent at the bottom is eps_0's.

Fundamental sequences use the standard rules:

    (a + w^(b+1))[n]  = a + w^b * (n+1)
    (a + w^b)[n]      = a + w^(b[n])        (b a limit)
    the atom E0 is not a limit.

`steps(a, n)` counts how many times that rule must be applied, with the same n
each time, until 0 is reached.  That is exactly a machine's decrement count.
"""

import sys

sys.setrecursionlimit(10000)


class Ord:
    """CNF term list: [(exponent, coeff), ...] with exponents descending."""

    __slots__ = ('terms',)

    def __init__(self, terms=()):
        self.terms = tuple(terms)

    def is_zero(self):
        return not self.terms

    def is_atom(self):
        return (len(self.terms) == 1 and self.terms[0][0] is None
                and self.terms[0][1] == 1)

    def __eq__(self, other):
        if not isinstance(other, Ord):
            return NotImplemented
        return self.terms == other.terms

    def __hash__(self):
        return hash(self.terms)

    def __repr__(self):
        if self.is_zero():
            return '0'
        return ' + '.join(
            ('e0+1' if e is None else f'w^({e!r})') + (f'*{c}' if c > 1 else '')
            for e, c in self.terms)


ZERO = Ord()
E0 = Ord(((None, 1),))


def add(a, b):
    """CNF addition: a + b, absorbing b's leading terms into a's tail."""
    if b.is_zero():
        return a
    if a.is_zero():
        return b
    out = list(a.terms)
    for e, c in b.terms:
        if out and out[-1][0] == e:
            out[-1] = (e, out[-1][1] + c)
        else:
            out.append((e, c))
    return Ord(out)


def mul_pow(exp, coeff):
    """w^exp * coeff."""
    if coeff <= 0:
        return ZERO
    return Ord(((exp, coeff),))


def top(a):
    return a.terms[-1]


def rest(a):
    return Ord(a.terms[:-1])


def pred(a):
    """Predecessor of a successor ordinal."""
    e, c = top(a)
    if c > 1:
        return add(rest(a), mul_pow(e, c - 1))
    return rest(a)


def is_limit(a):
    if a.is_zero():
        return False
    if a.is_atom():
        return True              # eps_0 = sup of the omega towers over 1
    e, c = top(a)
    if c > 1:
        return False
    if e is None:
        return False
    return not e.is_zero()       # w^e is a limit for every e != 0


def succ_exp(e):
    """e + 1 for a CNF exponent."""
    return add(e, Ord(((ZERO, 1),)))


def fs(a, n):
    """The n-th member of a's fundamental sequence."""
    assert is_limit(a), a
    if a.is_atom():
        return wraps(n)          # eps_0[n] = a tower of n omegas over 1
    head, (e, c) = rest(a), top(a)
    if not is_limit(e):
        # w^(b+1) * 1 -> w^b * (n+1)
        return add(head, mul_pow(pred(e), n + 1))
    return add(head, mul_pow(fs(e, n), 1))


def hardy(a, n, cap=3 * 10 ** 6):
    """H_a(n): descend a to 0, incrementing n at every successor step.

    This is the quantity a machine's step count tracks -- a fixed-index descent
    collapses immediately, while Hardy's growing index is what makes eps_0 and
    eps_1 far apart.  Returns (value, None) or (None, steps) if it hits the cap.
    """
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


def wraps(n):
    """A tower of n omegas over 1: n=0 is 1, n=1 is w, n=2 is w^w, ..."""
    a = Ord(((ZERO, 1),))
    for _ in range(n):
        a = Ord(((a, 1),))
    return a


def su_eps0():
    """eps_0 + 1: the bottom of the eps_1 tower."""
    return add(E0, Ord(((ZERO, 1),)))


def tower(h, coeff=1):
    """w^w^...^(eps_0+1) with h wraps; h=0 is eps_0+1 itself."""
    a = su_eps0()
    for _ in range(h):
        a = Ord(((a, coeff),))
    return a


def check():
    print('eps_1 descent model: steps to 0 from the h-th member of eps_1s sequence')
    ok = True
    for h in range(0, 4):
        row = []
        for n in (1, 2, 3):
            a = tower(h)
            v, st = hardy(a, n)
            if v is None:
                row.append(f'n={n}: >{st} steps')
            else:
                row.append(f'n={n}: {v}' + (f' ({v.bit_length()} bits)' if v > 1000 else ''))
        print(f'  tower height {h} ({tower(h)!r})')
        print('    ', '   '.join(row))
    # the atom must be reached, not expanded
    assert is_limit(tower(1)) and is_limit(E0) and not is_limit(su_eps0())
    print('atom is not a limit, tower(1) is: OK')
    return ok


if __name__ == '__main__':
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
