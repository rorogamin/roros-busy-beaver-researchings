"""The omega*2 descent as a chain machine.

State (a, b) is the ordinal w*a + b, with a and b unary naturals.

This is the smallest rung whose fundamental sequence leaves a single term:
    (w*2)[n] = w + n
is a sum, so unlike eps1_chain the chain has to carry two coefficients.
The moves are the standard ones:

    (a, b), b > 0     -> (a, b-1), index n += 1        pred
    (a, 0), a > 0     -> (a-1, n), index unchanged     fs
    (0, 0)            -> halt

The descent length is Hardy's H_{w*a+b}(n), and from (2, 0) it has the closed
form 3n + 2: fs to (1, n), n preds to (1, 0), fs to (0, 2n), 2n preds to zero.

This is the RULE layer, not a step-count claim: a machine at level w*2 has to
follow these moves with its tape state, and the FGH iteration count is a
separate obligation (f_{w*2}(n) = f_w^{n^n}(n)).

Run: python tools/omega2_chain.py
"""

import sys


# ------------------------------------------------------------------- the model

def is_zero(st):
    a, b = st
    return a == 0 and b == 0


def is_limit(st):
    a, b = st
    return b == 0 and a > 0


def pred(st):
    a, b = st
    assert b > 0, 'pred of a limit'
    return (a, b - 1)


def fs(st, n):
    a, b = st
    assert b == 0 and a > 0, 'fs of a non-limit'
    return (a - 1, n)


class Halt(Exception):
    pass


def step(st, n):
    """One descent move.  Returns (state, n, kind); raises Halt at zero."""
    if is_zero(st):
        raise Halt
    if is_limit(st):
        return fs(st, n), n, 'fs'
    return pred(st), n + 1, 'pred'


def run(st, n, limit=1_000_000):
    """Descend to zero.  Returns (moves, final n), or (None, n) past the cap."""
    moves = 0
    while not is_zero(st):
        st, n, _ = step(st, n)
        moves += 1
        if moves > limit:
            return None, n
    return moves, n


def hardy(st, n, cap=1_000_000):
    """The descent counted directly, without calling step()."""
    a, b = st
    moves = 0
    while a or b:
        if b:
            b -= 1
            n += 1
        else:
            a -= 1
            b = n
        moves += 1
        if moves > cap:
            return None, moves
    return n, moves


# ---------------------------------------------------------------- the checks

def check_fs():
    print('fundamental sequences below w*2')
    ok = True
    for k in range(4):
        st = (k + 1, 0)
        row = []
        for n in range(5):
            got = fs(st, n)
            want = (k, n)
            same = got == want
            ok = ok and same
            row.append(f'n={n}:{got}')
        print(f'  fs({st}) -> ' + ' '.join(row) + ('' if ok else '  MISMATCH'))
    # the corrected identity, in ordinal terms: (w*2)[n] = w + n
    print('  (w*2)[n] == w + n: ' +
          ('OK' if all(fs((2, 0), n) == (1, n) for n in range(6)) else 'FAIL'))
    return ok


def check_decrease():
    print('strict decrease at every move')
    bad = 0
    for a in range(5):
        for b in range(5):
            for n in range(1, 4):
                st = (a, b)
                if is_zero(st):
                    continue
                st2, _, kind = step(st, n)
                # value w*a+b decreases lexicographically in (a, b) here
                dec = st2[0] < a or (st2[0] == a and st2[1] < b)
                if not dec:
                    bad += 1
                    print(f'  NOT DECREASING {kind}: {st} -> {st2}')
    print(f'  all (a,b) <= 4 x 4, n=1..3: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_lengths():
    print('lengths: chain run against hardy()')
    ok = True
    for a in range(5):
        for b in range(4):
            for n in (1, 2, 3):
                st = (a, b)
                mv, _ = run(st, n)
                val, stc = hardy(st, n)
                same = mv == stc
                ok = ok and same
                if not same:
                    print(f'  MISMATCH {st} n={n}: chain {mv} hardy {stc}')
    print('  all a<=4, b<=3, n=1..3: ' + ('OK' if ok else 'FAILURES'))
    return ok


def check_closed_form():
    print('closed form from w*2')
    ok = True
    for n in range(0, 20):
        mv, fin = run((2, 0), n)
        want = 3 * n + 2
        same = mv == want
        ok = ok and same
        if not same:
            print(f'  n={n}: got {mv}, want {want}')
    print('  run((2,0), n) == 3n+2 for n=0..19: ' + ('OK' if ok else 'FAILURES'))
    return ok


def main():
    ok = check_fs()
    ok = check_decrease() and ok
    ok = check_lengths() and ok
    ok = check_closed_form() and ok
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
