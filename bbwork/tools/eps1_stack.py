"""The eps_1 stack model: eps1_chain's (p, chain, n) with the wraps kept in place.

`tools/eps1_chain.py` is the checked rule set of record: state (p, chain, n),
where p counts the wraps above val(chain) (each a whole omega: `full` iterates
mul_pow(v, 1)), and `normalise` moves trailing unit entries out of the chain
into p.  The table of record (tools/eps1_table.py, 150 raw / 143 refined
states) transcribes those movements literally and pays for the bookkeeping:
the park lives far left of the chain, the index far right, and every
cross-field edit (copy, absorb, spend, fs-limit) is a round trip between
fields that a 2-symbol head cannot tell apart except by walking.

This module is the model side of the reset proposed in EPS1_67_PLAN.md: the
same moves re-derived as *local top-of-stack edits*, with the wraps represented
in place -- a trailing block of unit rungs -- instead of as a counter parked
far from the block it counts.  The wraps are a structural part of the tower:

    stack := [r0, r1, ..., rk]      bottom-first rungs
    r0    := ('E01',) | ('E0',) | ('N', c)    the bottom: the atom eps_0+1,
               the atom eps_0, or a finite coefficient c >= 1
    r_i   := ('N', c)    for i >= 1            coefficients c >= 1

The unit rungs at the top of the stack *are* eps1_chain's p, so
`normalise`'s park bookkeeping disappears: no state carries a count that
lives apart from the block it counts.  `model_of`/`stack_of` are the
bijection, including eps1_chain's own corners (its normalise guard
len(chain) > 1 means the bottom unit rung is never folded into p):

    model_of:  p     = the number of trailing ('N', 1) rungs, capped so the
                     chain part stays nonempty (the all-unit stack keeps its
                     bottom rung as the chain's [NUM(1)], exactly as
                     eps1_chain's guard does); the sole unit rung alone is
                     p=0, chain=[NUM(1)]
               chain = the rest, r0 mapped back to its entry kind
    stack_of:  rungs = chain entries ++ [('N', 1)] * p

and `stack_step` is one move expressed only on the top of the ladder:

    successor (no trailing unit rung above the acting entry)
      ('N', c), c >= 2            -> c := c - 1          (index bumped)
      [('N', 1)] alone            -> []                  (the chain was 1)
      [('E01',)] alone            -> [('E0',)]           (eps_0+1 -> eps_0)
    limit (the fs move: locate the acting site first, then edit)
      m = the trailing unit rungs; if every rung is a unit (k >= 2, so the
          site is the bottom)     -> [(n+1)] ++ 1^(k-2)
      j = the topmost rung with count >= 2; if j == 0 AND r0 is an atom
          (all rungs above it are units):
          [('E01',)]               -> [E0, (n+1)] ++ 1^(m-1)  (w^(eps_0+1))
          [('E0',)], m = s         -> 1^(n+s+1)               (eps_0[n],
                                      with s leading omegas: the naked
                                      atom m=0 gives n+1 units exactly)
      otherwise                    -> ...[e_j-1, (n+1), 1^(m-1)]

Every move touches exactly: the top unit rung, the acting site, and the rung
written next to it.  That locality is what a <= 67-state table needs: the fs
move's n+1 marks are written at one site, instead of shuttled between three
separated fields.  (The tape still needs an n-source for that write; where it
lives is the stack table's own concern -- see EPS1_67_PLAN.md.)

Run: python tools/eps1_stack.py
     checks the bijection, 400 chains x 4 moves against eps1_chain.step
     (bookkeeping-exact) and against eps1_descent's fs/pred (value-exact),
     and the descent lengths against hardy() on the eps_1 members.
"""

import sys
import random

sys.path.insert(0, 'tools')

import eps1_descent as D
import eps1_chain as C
from eps1_descent import Ord, ZERO, add, mul_pow, fs, pred, is_limit, E0

ATOM = E0                                     # eps_0, a limit
ATOM1 = C.ATOM1                               # eps_0 + 1, a successor
NUM = lambda c: Ord(((ZERO, c),))

RU = ('N', 1)                                 # a unit rung


def rn(c):
    return ('N', c)


# ------------------------------------------------------------------ the value

def stack_val(rungs):
    """The ordinal of a stack."""
    if not rungs:
        return ZERO
    k0 = rungs[0]
    if k0 == ('E0',):
        v = ATOM
    elif k0 == ('E01',):
        v = ATOM1
    else:
        assert k0[0] == 'N' and k0[1] >= 1, k0
        v = NUM(k0[1])
    for _, c in rungs[1:]:
        assert c >= 1
        v = mul_pow(v, c)
    return v


# ----------------------------------------------------------------- bijection

def entry2rung(x):
    """eps1_chain's first entry -> the bottom rung."""
    if x == ATOM:
        return ('E0',)
    if x == ATOM1:
        return ('E01',)
    assert len(x.terms) == 1 and x.terms[0][0] == ZERO, x
    return ('N', x.terms[0][1])


def rung2entry(k):
    """The bottom rung -> eps1_chain's first entry."""
    if k == ('E0',):
        return ATOM
    if k == ('E01',):
        return ATOM1
    assert k[0] == 'N'
    return NUM(k[1])


def model_of(rungs):
    """stack -> (p, chain), eps1_chain's canonical bookkeeping."""
    if not rungs:
        return 0, []
    if rungs == [RU]:
        # the sole unit rung: 1, never folded into p (eps1_chain's guard)
        return 0, [NUM(1)]
    p = 0
    while p < len(rungs) - 1 and rungs[len(rungs) - 1 - p] == RU:
        p += 1
    head = rungs[:len(rungs) - p]
    return p, [rung2entry(head[0])] + [c for _, c in head[1:]]


def stack_of(p, chain):
    """(p, chain) -> stack.  The inverse of `model_of` on canonical states."""
    if not chain:
        assert p == 0, (p, chain)
        return []
    return [entry2rung(chain[0])] + [rn(c) for c in chain[1:]] + [RU] * p


# -------------------------------------------------------------------- moves

class Halt(Exception):
    pass


def is_succ(rungs):
    """Is val(stack) a successor ordinal?  Structural, so it is cheap."""
    if not rungs:
        return False
    last = rungs[-1]
    if last[0] == 'N':
        return last[1] >= 2 or len(rungs) == 1
    # the atoms sit only at the bottom; eps_0 is a limit
    return last[0] == 'E01' and len(rungs) == 1


def stack_step(rungs, n):
    """One move as a top-of-stack edit.  Returns (rungs, n); raises Halt."""
    if not rungs:
        raise Halt
    if is_succ(rungs):
        last = rungs[-1]
        n += 1                                  # the Hardy index bumps here
        if last[0] == 'E01':
            return [('E0',)], n                 # eps_0+1 -> eps_0
        if last[1] <= 1:
            return rungs[:-1], n                # the sole unit: the chain was 1
        return rungs[:-1] + [rn(last[1] - 1)], n

    # ---- limit: the unit block above the acting site is the wraps, in place
    m = 0                                       # trailing unit rungs
    while len(rungs) - 1 - m >= 0 and rungs[len(rungs) - 1 - m] == RU:
        m += 1
    if m == len(rungs):
        # every rung is a unit (k >= 2, no atom bottom): the site is the bottom
        return [rn(n + 1)] + [RU] * (len(rungs) - 2), n
    j = len(rungs) - 1 - m                      # topmost rung with c >= 2
    if j == 0 and rungs[0][0] != 'N':
        # the acting site IS the atom bottom, all rungs above it are units
        if rungs[0][0] == 'E01':
            return [('E0',), rn(n + 1)] + [RU] * (m - 1), n
        return [RU] * (n + m + 1), n             # eps_0[n] lifted by m omegas
    assert rungs[j][1] >= 2 and j >= 0
    return rungs[:j] + [rn(rungs[j][1] - 1), rn(n + 1)] + [RU] * (m - 1), n


def stack_run(rungs, n, limit=200000):
    """Descend to zero.  Returns (moves, final n)."""
    moves = 0
    while True:
        try:
            rungs, n = stack_step(rungs, n)
        except Halt:
            return moves, n
        moves += 1
        if moves > limit:
            return None, n


# ------------------------------------------------------------------- checks

def random_stack(rng, depth):
    """A random stack: bottom kind + free counts, unnormalised."""
    bottom = rng.choice([rn(1), rn(2), rn(3), ('E0',), ('E01',)])
    rungs = [bottom]
    for _ in range(rng.randint(0, depth)):
        rungs.append(rn(rng.choice([1, 1, 2, 3])))
    return rungs


def _random_normalised(rng, depth):
    """A random *normalised* (p, chain): eps1_chain's own canonical states."""
    p = rng.randint(0, 2)
    chain = [rng.choice([C.NUM(1), C.NUM(2), C.NUM(3), C.ATOM, C.ATOM1])]
    for _ in range(rng.randint(1, depth)):
        chain.append(rng.choice([1, 1, 2, 3]))
    return p, chain


def check_bijection(trials=400, seed=13, depth=4):
    print('the bijection: val(stack) == full(p, chain), and it round trips')
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        s = random_stack(rng, depth)
        p, ch = model_of(s)
        if stack_val(s) != C.full(p, ch):
            bad += 1
            print(f'  VALUE MISMATCH stack={s} -> p={p} chain={ch}')
            print(f'    stack_val {stack_val(s)!r} vs full {C.full(p, ch)!r}')
            continue
        s2 = stack_of(p, ch)
        if s2 != s:
            bad += 1
            print(f'  ROUNDTRIP MISMATCH stack={s} -> ({p},{ch}) -> {s2}')
    print(f'  {trials} stacks: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_moves(trials=400, seed=11, depth=4):
    print('every move: stack_step vs eps1_chain.step, bookkeeping-exact')
    print('            and the decoded value against eps1_descent (fs/pred)')
    rng = random.Random(seed)
    bad = 0
    halts = 0
    for _ in range(trials):
        p, ch = _random_normalised(rng, depth)
        n = rng.randint(1, 3)
        rungs = stack_of(p, ch)
        V = C.full(p, ch)
        for _ in range(4):
            if V.is_zero():
                break
            try:
                p2, c2, n2, kind = C.step(p, ch, n)
            except C.Halt:
                bad += 1
                print(f'  EPS1_CHAIN HALTED EARLY: p={p} chain={ch} n={n}')
                break
            try:
                rungs2, n2s = stack_step(rungs, n)
            except Halt:
                bad += 1
                print(f'  STACK HALTED EARLY: rungs={rungs} n={n}')
                break
            p2s, c2s = model_of(rungs2)
            if (p2s, c2s) != (p2, c2) or n2s != n2 or (kind == 'pred') != (n2 == n + 1):
                bad += 1
                print(f'  MISMATCH {kind}: p={p} chain={ch} n={n} (stack {rungs})')
                print(f'    eps1_chain -> ({p2}, {c2}) n={n2}')
                print(f'    stack      -> ({p2s}, {c2s}) n={n2s}')
                break
            want = fs(V, n) if kind == 'fs' else pred(V)
            if C.full(p2s, c2s) != want:
                bad += 1
                print(f'  VALUE MISMATCH {kind} at p={p} chain={ch} n={n}')
                print(f'    model wants {want!r}, states give {C.full(p2s, c2s)!r}')
                break
            p, ch, n, V, rungs = p2, c2, n2, want, rungs2
            if not rungs:
                halts += 1
                break
    print(f'  {trials} chains x 4 moves ({halts} reaching the empty stack): '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_lengths(kmax=3, cap=300000):
    print()
    print('lengths: the stack machine against hardy(), from the eps_1 members')
    ok = True
    for k in range(0, kmax + 1):
        V = D.tower(k)
        p, ch = C.chain_of(V)
        rungs0 = stack_of(p, ch)
        for n in (1, 2, 3):
            mv, _ = stack_run(list(rungs0), n, limit=cap)
            v, st = D.hardy(V, n, cap=cap)
            same = (mv is None and v is None) or (mv == st)
            ok = ok and same
            print(f'    member {k} n={n}: stack '
                  f'{mv if mv is not None else ">" + str(cap)} vs hardy {st}'
                  + ('' if same else '   MISMATCH'))
    print('  lengths match where both run: ' + ('OK' if ok else 'FAILURES'))
    return ok


def main():
    ok = check_bijection()
    ok = check_moves() and ok
    ok = check_lengths() and ok
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
