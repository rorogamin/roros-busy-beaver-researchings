"""The eps_1 descent as a chain machine, checked against the ordinal model.

The machine's state is (p, chain, n):

    p      wraps: the ordinal is w^p(val chain), p a unary count on the tape
    chain  the active chain, bottom-first, entries unary, with the atom eps_0
           (and eps_0+1) allowed as the bottom, since that is the base eps_1's
           sequence sits on
    n      the index, bumped at every predecessor step

val([b0, b1, ..., bm]) = w^(w^(...^(b0)*b1)...)*bm

The moves below are the tape operations of the design of record, written at the
level of the chain so they can be checked against `eps1_descent` exactly: after
every move the decoded ordinal must equal the model's fs or pred of the previous
one, with the index bumped exactly on predecessor moves.  Once this is green the
same moves are transcribed into a 2-symbol table.

Why the representation is enough: descending eps_1[n] = the tower of n omegas
over eps_0+1 keeps the ordinal a single term throughout -- fs and pred of a
single term are single terms -- so the chain never needs to carry a sum, except
the eps_0+1 at the bottom, which is the atom with a flag.

Run: python tools/eps1_chain.py
"""

import sys
import random

sys.path.insert(0, 'tools')

import eps1_descent as D
from eps1_descent import Ord, ZERO, add, mul_pow, fs, pred, is_limit, E0

NUM = lambda c: Ord(((ZERO, c),))
ATOM = E0
ATOM1 = add(E0, NUM(1))


# ------------------------------------------------------------------ decoding

def val(chain):
    """The ordinal of a chain.  The empty chain is 0."""
    if not chain:
        return ZERO
    v = chain[0] if isinstance(chain[0], Ord) else NUM(chain[0])
    for b in chain[1:]:
        v = mul_pow(v, b)
    return v


def full(p, chain):
    """w^p(val chain)."""
    v = val(chain)
    for _ in range(p):
        v = mul_pow(v, 1)
    return v


# -------------------------------------------------------------------- moves

class Halt(Exception):
    pass


def is_atom(x):
    return isinstance(x, Ord) and x.is_atom()


def is_atom1(x):
    return isinstance(x, Ord) and not x.is_zero() and x == ATOM1


def is_succ(chain):
    """Is val(chain) a successor ordinal?  Structural, so it is cheap."""
    top = chain[-1]
    if isinstance(top, Ord):
        return not is_atom(top)                 # eps_0 is a limit, the rest are not
    return top >= 2


def num_of(x):
    return x.terms[0][1]


def pred_chain(chain):
    """The chain for val(chain) - 1, when val(chain) is a successor."""
    top = chain[-1]
    if isinstance(top, Ord):
        if is_atom1(top):
            return [ATOM]
        c = num_of(top)
        return [NUM(c - 1)] if c > 1 else []
    assert top >= 2, 'pred_chain on a limit'
    return chain[:-1] + [top - 1]


def chain_fs(chain, n):
    """The chain for val(chain)[n], when val(chain) is a limit."""
    top = chain[-1]
    if isinstance(top, Ord):
        assert is_atom(top), 'single entry limit must be the atom'
        return [NUM(1)] + [1] * n               # eps_0[n] = tower of height n
    assert top == 1, 'top >= 2 is a successor'
    below = chain[-2] if len(chain) >= 2 else None
    if isinstance(below, Ord):
        if is_atom(below):                      # w^(eps_0) -> w^(tower n)
            return [NUM(1)] + [1] * (n + 1)
        if is_atom1(below):                     # w^(eps_0+1) -> w^eps_0*(n+1)
            return [ATOM, n + 1]
        c = num_of(below)
        if c >= 2:                              # w^(w^0*c) -> w^(w^0*(c-1))*(n+1)
            return [NUM(c - 1), n + 1]
        return [NUM(n + 1)]                     # w^1 -> n+1
    assert below is not None
    if below >= 2:                              # w^(E)*1 -> w^(E-1)*(n+1)
        return chain[:-2] + [below - 1, n + 1]
    return chain_fs(chain[:-1], n) + [1]        # exponent is a limit: step it


def normalise(p, chain):
    """Absorb unit entries at the top into the wrap count.

    The invariant is that the chain's top entry is the acting one, so every unit
    entry above it lives in p instead of on the chain.  Erasing a top 1 and
    incrementing p preserves the value: w^(w^p(X)) = w^(p+1)(X).
    """
    while len(chain) > 1 and chain[-1] == 1:
        chain = chain[:-1]
        p += 1
    return p, chain


def step(p, chain, n):
    """One move.  Returns (p, chain, n, kind); raises Halt at zero."""
    if not chain:
        raise Halt
    if is_succ(chain):
        head = pred_chain(chain)
        if p == 0:                              # pred
            p2, c2 = normalise(0, head)          # the empty chain is 0
            return p2, c2, n + 1, 'pred'
        # w^p(E+1) -> w^(p-1)(w^E * (n+1)): one wrap is spent on the coefficient
        chain2 = (head + [n + 1]) if head else [NUM(n + 1)]
        p2, c2 = normalise(p - 1, chain2)
        return p2, c2, n, 'fs'

    # the chain's value is a limit: step it, the wraps are untouched
    p2, c2 = normalise(p, chain_fs(chain, n))
    return p2, c2, n, 'fs'


def run(p, chain, n, limit=200000):
    """Descend to zero, exactly mirroring hardy().  Returns (moves, final n)."""
    moves = 0
    while True:
        try:
            p, chain, n, kind = step(p, chain, n)
        except Halt:
            return moves, n
        moves += 1
        if moves > limit:
            return None, n


# ------------------------------------------------------------- the checks

def chain_of(V):
    """Decode an Ord as (p, chain) -- for starting a run from the model side."""
    p = 0
    v = V
    while True:
        if v.is_atom():
            return p, [ATOM]
        if v == ATOM1:
            return p, [ATOM1]
        if len(v.terms) != 1:
            raise ValueError(f'not a chain: {v!r}')
        e, c = v.terms[0]
        if e.is_zero():
            return p, [NUM(c)]
        p += 1
        v = e


def check_against_model(trials=400, seed=11, depth=4):
    print('every move against eps1_descent, decoded after each move')
    rng = random.Random(seed)

    def chain(d):
        if d == 0:
            return [rng.choice([NUM(1), NUM(2), NUM(3), ATOM, ATOM1])]
        return [rng.choice([NUM(1), NUM(2), NUM(3), ATOM, ATOM1])] + \
               [rng.choice([1, 1, 2, 3]) for _ in range(rng.randint(1, d))]

    bad = 0
    for _ in range(trials):
        p = rng.randint(0, 2)
        c = chain(depth)
        n = rng.randint(1, 3)
        V = full(p, c)
        for _ in range(4):
            if V.is_zero():
                break
            try:
                p2, c2, n2, kind = step(p, c, n)
            except Halt:
                bad += 1
                print(f'  HALT TOO EARLY: p={p} chain={c} n={n} value={V!r}')
                break
            want = fs(V, n) if kind == 'fs' else pred(V)
            got = full(p2, c2)
            if got != want or (kind == 'pred') != (n2 == n + 1):
                bad += 1
                print(f'  MISMATCH {kind}: p={p} chain={c} n={n}')
                print(f'    model says {want!r}')
                print(f'    machine gives {got!r} (p={p2} chain={c2} n={n2})')
                break
            p, c, n, V = p2, c2, n2, want
    print(f'  {trials} chains x 4 moves: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_lengths():
    print()
    print('lengths: the chain machine against hardy() on the model, from eps_1[n]')
    print('  (eps_1[n] = the tower of n omegas over eps_0+1)')
    ok = True
    for k in range(0, 4):
        V = D.tower(k)
        p, c = chain_of(V)
        for n in (1, 2, 3):
            mv, _ = run(p, c, n, limit=300000)
            v, st = D.hardy(V, n, cap=300000)
            same = (mv is None and v is None) or (mv == st)
            ok = ok and same
            print(f'    member {k} n={n}: chain {mv if mv is not None else ">"+str(300000)}'
                  f' vs hardy {st}' + ('' if same else '   MISMATCH'))
    print('  lengths match where both run: ' + ('OK' if ok else 'FAILURES'))
    return ok


def check_blank_obligation():
    """eps_1[3] = w^w^w^(eps_0+1): the blank-tape obligation of rule 6."""
    print()
    V = D.tower(3)
    p, c = chain_of(V)
    print(f'the obligation: eps_1[3] = {V!r}')
    print(f'  as a chain: p={p} chain={c}  (bottom is the atom with its +1)')
    print(f'  a blank-tape build writes exactly that, then runs the moves above')
    # first moves, decoded, for the record
    n = 3
    for i in range(6):
        try:
            p, c, n, kind = step(p, c, n)
        except Halt:
            print('  halted')
            break
        print(f'  move {i + 1} ({kind}): p={p} chain={c} n={n}  ->  {full(p, c)!r}')
    return True


def main():
    ok = check_against_model()
    ok = check_lengths() and ok
    check_blank_obligation()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
