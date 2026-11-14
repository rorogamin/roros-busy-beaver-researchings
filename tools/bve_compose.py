"""Compose the 23-state cursor with the predecessor suffix-truncation arm.

The composed table starts at the first zero of the H/E separator.  Its first
five states are the cursor's prefix and walk left to the duplicate-flag cell
of the LAST header.  At that cell the cursor's flag dispatch is rerouted:

  flag 0: the ordinary 18-state cursor core runs and halts unchanged on the
          last exponent separator (the FS arm is not built).
  flag 1: zero the flag, move to the first op cell, and enter the predecessor
          arm at its second state; the predecessor zeros the remaining four
          op cells and truncates the E suffix.

The table is 46 states (0..45): 23 cursor states, with core state 0's flag-1
branch redirected, plus predecessor states 1..23 shifted to 23..45.  The
extra predecessor state is the zero-gap normaliser, so a raw predecessor
output can be read by a second predecessor pass without a shift.

Run: python tools/bve_compose.py
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_two_bank as T
import bve_cursor
import bve_pred
from tm import TM

CURSOR = dict(bve_cursor.TABLE_HEND)
CURSOR[(5, 1)] = (0, 'R', 23)   # zero flag, enter pred state 1 at op cell 1

PRED = {}
for (_s, _r), (_w, _d, _n) in bve_pred.TABLE.items():
    if _s == 0:
        continue                # the cursor flag read performs pred state 0
    PRED[(_s + 22, _r)] = (
        _w, _d, None if _n is None else _n + 22)

TABLE = {}
TABLE.update(CURSOR)
TABLE.update(PRED)
N_STATES = 46


def run(tape, head, max_steps=200_000):
    m = TM(N_STATES, TABLE)
    tape = dict(tape)
    state = 0
    for steps in range(max_steps):
        k = (state, tape.get(head, 0))
        if k not in TABLE:
            return True, tape, head, state, steps
        write, direction, nxt = TABLE[k]
        tape[head] = write
        head += 1 if direction == 'R' else -1
        state = nxt
    return False, tape, head, state, max_steps


def tape_string(tape):
    lo = min(tape) if tape else 0
    hi = max(tape) if tape else 0
    return ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def term_tape(v):
    h, e = T.banks(v)
    return T.FIELD + h + T.DELIM + e + T.FIELD


def h_end_of(v):
    return len(T.FIELD) + len(T.banks(v)[0])


def check(n_each=200):
    rng = random.Random(41)

    def term(d):
        if d <= 0:
            return rng.choice((ZERO, ONE))
        k = rng.randrange(4)
        if k == 0:
            return phi(0, term(d - 1))
        if k == 1:
            return phi(1, term(d - 1))
        if k == 2:
            return add(term(d - 1), term(d - 1))
        return add(phi(0, term(d - 1)), term(d - 1))

    one_terms = [add(ONE, ONE), add(phi(0, ONE), phi(0, ONE)),
                 add(B.epsilon0(), B.epsilon0()), add(B.epsilon1(), B.epsilon1()),
                 add(add(ONE, ONE), ONE)]
    while len(one_terms) < n_each + 5:
        base = term(2)
        v = add(base, base)
        if len(v.terms) >= 2 and v.terms[-1] == v.terms[-2]:
            one_terms.append(v)

    zero_terms = [ONE, B.epsilon1(), add(phi(0, ONE), ONE),
                  phi(0, add(ONE, ONE))]
    while len(zero_terms) < n_each + 4:
        v = term(3)
        if len(v.terms) < 2 or v.terms[-1] != v.terms[-2]:
            zero_terms.append(v)

    bad = 0
    for group, terms in (('flag1', one_terms), ('flag0', zero_terms)):
        for idx, v in enumerate(terms):
            is_dup = (len(v.terms) >= 2 and v.terms[-1] == v.terms[-2])
            if group == 'flag1' and not is_dup:
                bad += 1
                print(f'  BAD FLAG1 TERM {idx}: {v!r}')
                continue
            if group == 'flag0' and is_dup:
                bad += 1
                print(f'  BAD FLAG0 TERM {idx}: {v!r}')
                continue
            tape_s = term_tape(v)
            tape = {i: int(c) for i, c in enumerate(tape_s)}
            ok, out, head, state, steps = run(tape, h_end_of(v))
            if not ok:
                bad += 1
                print(f'  {group} NO HALT {idx}: {v!r}')
                continue
            try:
                got = T.from_tape(tape_string(out))
            except Exception as exc:
                bad += 1
                print(f'  {group} DECODE {idx}: {v!r}')
                print(f'    {type(exc).__name__}: {exc}')
                print(f'    in  {tape_s}')
                print(f'    out {tape_string(out)}')
                continue
            want = B.pred(v) if group == 'flag1' else v
            if got != want:
                bad += 1
                print(f'  {group} FAIL {idx}: {v!r}')
                print(f'    got  {got!r}')
                print(f'    want {want!r}')
    print(f'  flag1: {len(one_terms)} terms; flag0: {len(zero_terms)} terms: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_raw_chain(n_terms=20):
    """Feed one raw predecessor output directly into a second predecessor."""
    rng = random.Random(43)

    def term(d):
        if d <= 0:
            return rng.choice((ZERO, ONE))
        k = rng.randrange(4)
        if k == 0:
            return phi(0, term(d - 1))
        if k == 1:
            return phi(1, term(d - 1))
        if k == 2:
            return add(term(d - 1), term(d - 1))
        return add(phi(0, term(d - 1)), term(d - 1))

    def triple(base):
        return add(add(base, base), base)

    terms = [triple(ONE), triple(phi(0, ONE)), triple(B.epsilon1()),
             triple(add(phi(0, ONE), ONE))]
    while len(terms) < n_terms + 4:
        terms.append(triple(term(1)))

    bad = 0
    checked = 0
    for idx, v in enumerate(terms):
        if len(v.terms) < 3 or v.terms[-1] != v.terms[-2]:
            bad += 1
            print(f'  RAW CHAIN BAD TEST {idx}: {v!r}')
            continue
        raw = term_tape(v)
        cells = {i: int(c) for i, c in enumerate(raw)}
        ok, out, _head, _state, _steps = run(cells, h_end_of(v))
        if not ok:
            bad += 1
            print(f'  RAW CHAIN NO HALT {idx}: {v!r}')
            continue
        raw = tape_string(out)
        got = T.from_tape(raw)
        want = B.pred(v)
        if got != want:
            bad += 1
            print(f'  RAW CHAIN 1 FAIL {idx}: {v!r}')
            print(f'    got  {got!r}')
            print(f'    want {want!r}')
            continue
        if len(got.terms) < 2 or got.terms[-1] != got.terms[-2]:
            bad += 1
            print(f'  RAW CHAIN NOT DUP {idx}: {got!r}')
            continue
        cells = {i: int(c) for i, c in enumerate(raw)}
        ok, out, _head, _state, _steps = run(cells, h_end_of(got))
        if not ok:
            bad += 1
            print(f'  RAW CHAIN 2 NO HALT {idx}: {got!r}')
            continue
        got2 = T.from_tape(tape_string(out))
        want2 = B.pred(got)
        if got2 != want2:
            bad += 1
            print(f'  RAW CHAIN 2 FAIL {idx}: {got!r}')
            print(f'    got  {got2!r}')
            print(f'    want {want2!r}')
            continue
        checked += 1
    print(f'  raw predecessor chain: {checked}/{len(terms)} terms: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    for label, v in [('flag1', add(add(ONE, ONE), ONE)),
                     ('flag0', add(phi(0, ONE), ONE))]:
        tape_s = term_tape(v)
        tape = {i: int(c) for i, c in enumerate(tape_s)}
        hs = T.header_scan(tape_s)
        ok, out, head, state, steps = run(tape, h_end_of(v))
        s = tape_string(out)
        print(f'example: {label} {v!r}')
        print(f'  last flag {hs[-1][1]}')
        print(f'  halted={ok} state={state} head={head} steps={steps}')
        print(f'  decoded {T.from_tape(s)!r}')


def main():
    ok = check()
    ok = check_raw_chain() and ok
    if ok:
        print()
        example()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
