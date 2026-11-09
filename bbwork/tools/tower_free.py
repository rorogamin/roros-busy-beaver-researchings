"""The tower descent rewritten so that every growth happens at one free end.

`tools/tower_rules.py` validates four moves on a chain of coefficients, but it
cannot be put on a tape as it stands: move B sets the *top* coefficient to n+1,
and on a left-to-right chain the top sits between its neighbours, so growing it
means shifting the suffix, which two symbols cannot do.

This module is the same descent, rearranged so that the only coefficient that
ever grows sits at the free end of the tape.  Nothing here is a new system: the
step below is `tower_rules.step` with its recursion resolved, and `check`
compares it with the rules over every chain up to depth 4.

## The rearrangement

Write the chain top-first -- leftmost run = top of the tower -- as a list of run
lengths T = [t0, t1, ..., tk].  `tower_rules.step`'s case analysis only ever
asks about the first two runs:

    t0 >= 2                    A:  t0 -= 1
    t0 == 1, k == 0                the chain was 1, so it is 0
    t0 == 1, t1 >= 2           B:  t0 := n+1, t1 -= 1
    t0 == 1, t1 == 1           C:  keep t0, step the rest

and C only ever walks: it strips one leading 1 at a time until it reaches the
first run of size >= 2, where B fires (the run above the prefix is the one that
becomes n+1).  Resolving that walk gives, with j the first index >= 1 whose run
is >= 2,

    T' = [1]*(j-1) ++ [n+1] ++ [T[j]-1] ++ T[j+1:]

so the *position* that grows is j-1, i.e. just under the leading block of 1s.
That block is the part that cannot sit at the free end -- it is above the growth
site.  So split the chain into

    park  m      = the number of leading 1s        (runs above the growth site)
    W            = the rest, W[0] >= 2 or W empty  (the working part)

and the step is

    m == 0                 A:  W[0] -= 1                (then re-split)
    m >= 1, W nonempty     B:  park m-1, W := [n+1, W[0]-1] ++ W[1:]
    m >= 1, W empty        W := [n+1], park m-2         (m == 1: the chain is 1)

Now every growth is at W[0] -- W's top, the free end of the tape -- and the park
is a count that only ever shrinks.  `W[0] -= 1` can leave W[0] == 1, in which
case the chain's leading 1 must join the park; that is re-splitting, not a move.

## What the tape does with this

    [free] 1^{W0} 0 1^{W1} 0 ... 0 1^{Wk}   0 0  1^m 0 0  1^n 0 ...

W top-first at the left, so its top run grows into free space (write n marks to
its left), the park is a count run, and the index is the source of n.  Every
descent move is a walk plus O(1) marks written at the left boundary, except that
`m` changes: growing m means lengthening the park run, which is done into the
two blanks between W's bottom run and the park, so that gap must never reach
zero -- `descent` reports the largest m a run ever needs, which is what the
layout budgets for.
"""

import itertools
import sys

sys.path.insert(0, 'tools')
import eps1_descent as D
import tower_rules as R


def clean(chain):
    """Drop the model's leading zeros: a 0 coefficient is an inert bottom term."""
    ch = list(chain)
    while ch and ch[0] == 0:
        ch.pop(0)
    return ch


def to_tape(chain):
    """Bottom-first chain (the model's order) -> run lengths, top first."""
    return list(reversed(clean(chain)))


def to_ord(T):
    return R.to_ord(list(reversed(list(T))))


def split(T):
    """Chain (top first) -> (park m, working part W) with W[0] >= 2 or W empty."""
    m = 0
    while m < len(T) and T[m] == 1:
        m += 1
    return m, list(T[m:])


def join(m, W):
    return [1] * m + list(W)


def step(T, n):
    """One move, on a top-first run list.  None means the chain became 0."""
    T = list(T)
    if not T:
        return None
    m, W = split(T)
    if not W:                                   # chain is [1]*m
        if m <= 1:
            return None
        return join(max(m - 2, 0), [n + 1])
    if m == 0:                                  # A on the top run
        W[0] -= 1
        return join(0, W)
    W = [n + 1, W[0] - 1] + W[1:]               # B, with the park spent
    return join(m - 1, W)


def check():
    print('free-end tower step (park + working part) vs tower_rules')
    tested = 0
    bad = 0
    for depth in range(1, 5):
        for tup in itertools.product(range(1, 4), repeat=depth):
            T = to_tape(tup)
            if not T or to_ord(T).is_zero():
                continue
            for n in (1, 2, 3):
                want_chain = R.step(tup, n)
                want = D.ZERO if want_chain is None else R.to_ord(clean(want_chain))
                got_chain = step(T, n)
                got = D.ZERO if got_chain is None else to_ord(got_chain)
                tested += 1
                if got != want:
                    bad += 1
                    if bad <= 10:
                        print(f'  MISMATCH T={T} n={n}: park -> {got_chain} '
                              f'({got!r}), rules -> {clean(want_chain or [])} ({want!r})')
    print(f'  {tested} cases' + (', all matching' if not bad else f', {bad} bad'))
    return bad == 0


def descent(T, n, limit=2_000_000):
    """Run to 0.  Returns steps, steps spent in each branch, max park seen."""
    steps = 0
    top = 0
    park_max = 0
    depth_max = len(T)
    T = list(T)
    while T is not None and steps < limit:
        m, W = split(T)
        if not W:
            top += 1
        elif m == 0:
            top += 1
        else:
            top += 1
        park_max = max(park_max, m)
        T = step(T, n)
        steps += 1
        if T is not None:
            depth_max = max(depth_max, len(T))
    return steps, park_max, depth_max


def check_lengths():
    print('  descent lengths (steps to 0) and the sizes a layout must budget for:')
    for T in ([1], [2], [3], [1, 1], [2, 1], [3, 1], [1, 1, 1], [1, 2],
              [1, 1, 2], [2, 1, 1], [1, 1, 1, 1], [1, 2, 1], [2, 2],
              [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]):
        for n in (1, 2, 3):
            s, pm, dm = descent(T, n, limit=400_000)
            tag = str(s) if s < 400_000 else '>4e5'
            print(f'    T={str(T):<18} n={n}: steps={tag:<9} '
                  f'max park={pm:<3} max depth={dm}')
    return True


if __name__ == '__main__':
    ok = check()
    check_lengths()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
