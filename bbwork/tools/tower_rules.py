"""The tower rewrite rules: four local moves, checked against the ordinal model.

An eps_1-level machine cannot be built by nesting loops.  Nesting a drive inside
a drive inside a drive gives a fixed tower height, i.e. a fixed ordinal below
eps_0 -- the loop structure is in the states, and states are fixed.  Nothing
below eps_0 is reachable that way, which is why the ladder machines measure f_3
and f_4 however large their counters get.

To get above eps_0 the *tower has to be on the tape*: the depth becomes data, and
the machine's four local moves walk an arbitrarily deep tower.  The tape holds

    [1^c0] 0 0 [1^c1] 0 0 [1^c2] ... 0 0 [1^ch]

meaning

    c0, then w^(c0) * c1, then w^(w^(c0) * c1) * c2, ...

so a chain [c0, ..., ch] denotes the ordinal obtained by folding w^(-)*ci from
the bottom.  Depth h is unbounded, which is what raises the level: sup over h of
the towers is eps_1.

The four moves, with n the index (the machine reads it off the bottom run):

  A. top coefficient > 1        -> decrement it          (predecessor)
  B. top coefficient 1, exponent a successor
                                -> decrement the exponent, top becomes n+1
                                   (that is  w^(b+1) [n] = w^b * (n+1))
  C. top coefficient 1, exponent a limit
                                -> step the exponent instead
                                   (that is  w^b [n] = w^(b[n]))
  D. depth 0                    -> decrement the bottom coefficient

Every move touches O(1) cells of the tape plus, in move B, writing n+1 marks at
the top.  This module checks that the moves implement exactly `fs` and `pred`
from `eps1_descent`, over every small chain and index -- so the tape rules and
the ordinal model agree before a single state is written.
"""

import itertools
import sys

sys.path.insert(0, 'tools')
import eps1_descent as D


def to_ord(chain):
    """Fold a chain into the model's CNF ordinals."""
    ch = list(chain)
    while ch and ch[-1] == 0:
        ch.pop()
    if not ch:
        return D.ZERO
    v = D.Ord(((D.ZERO, ch[0]),)) if ch[0] > 0 else D.ZERO
    for c in ch[1:]:
        if c == 0:
            return D.ZERO
        v = D.mul_pow(v, c)
    return v


def trim(chain):
    ch = list(chain)
    while ch and ch[-1] == 0:
        ch.pop()
    return ch


def step(chain, n):
    """One move of the tower machine; returns the new chain, or None below zero."""
    ch = trim(chain)
    if not ch:
        return None
    h = len(ch) - 1
    if ch[h] > 1:                                   # A
        ch[h] -= 1
        return ch
    if h == 0:                                      # D
        ch[0] -= 1
        return ch
    exp_chain = ch[:h]
    e = to_ord(exp_chain)
    if e == D.ZERO:                                 # w^0*1 = 1, so drop the term
        return exp_chain
    if not D.is_limit(e):                           # B
        ch[h] = n + 1
        ch[:h] = dec_chain(exp_chain)
        return ch
    sub = step(exp_chain, n)                        # C
    if sub is None:
        sub = []
    return list(sub) + [ch[h]]


def dec_chain(chain):
    """Predecessor of a chain whose ordinal is a successor."""
    ch = trim(chain)
    if not ch:
        return []
    h = len(ch) - 1
    if ch[h] > 1:
        ch[h] -= 1
        return ch
    if h == 0:
        ch[0] -= 1
        return ch
    return dec_chain(ch[:h]) + [ch[h]]


def check():
    print('tower rewrite rules vs the ordinal model')
    ok = True
    tested = 0
    chains = []
    for depth in range(0, 4):
        for tup in itertools.product(range(0, 4), repeat=depth + 1):
            if any(c == 0 for c in tup[:-1]):
                continue
            chains.append(tup)
    for chain in chains:
        a = to_ord(chain)
        if a.is_zero():
            continue
        for n in (1, 2, 3):
            got_chain = step(chain, n)
            got = to_ord(got_chain) if got_chain is not None else D.ZERO
            want = D.fs(a, n) if D.is_limit(a) else D.pred(a)
            tested += 1
            if got != want:
                ok = False
                print(f'  MISMATCH chain={chain} n={n}: '
                      f'step -> {got!r}, fs/pred -> {want!r}')
    print(f'  {tested} chain/index cases, all matching' if ok
          else f'  {tested} cases with mismatches')
    return ok


if __name__ == '__main__':
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
