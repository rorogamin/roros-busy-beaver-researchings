"""Predecessor suffix-truncation arm for the two-bank rBVE tape.

Entry: head on the duplicate-flag cell of the LAST header, with flag = 1.
Exit:  the last header (five cells) and the last exponent block plus its
       preceding 000 separator are overwritten with zeros.  The zeros become
       the new suffix boundaries, so no middle shift or copy is needed.

The table is 24 states (0..23).  It is the predecessor arm only: it assumes
the duplicate flag has already been established, and it does not choose
between predecessor and fundamental-sequence moves.

State 23 is the gap normaliser.  A previous predecessor leaves the surviving
E bank to the right of the zeroed suffix, so a second raw pass sees more than
three zeros after H.  State 23 skips that whole zero run and starts the E scan
at its first 1; the zero run is internal to the H/E gap and no cells move.

Run: python tools/bve_pred.py
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_two_bank as T
from tm import TM

# 0-4   zero the five cells of the last header
# 5-7   cross the H/E separator
# 8-11  scan E to the four-zero field end
# 12-15 walk left to the last 000 separator
# 16-22 zero from the separator through the field end
#
# (state, read) -> (write, direction, next)
TABLE = {
    # zero the header suffix
    **{(s, r): (0, 'R', s + 1) for s in range(5) for r in (0, 1)},
    # H/E separator; state 23 then skips the whole H/E zero gap.  The gap
    # grows when a previous predecessor zeroed a header suffix.
    (5, 0): (0, 'R', 6),
    (5, 1): (1, 'R', 6),
    (6, 0): (0, 'R', 7),
    (6, 1): (1, 'R', 7),
    (7, 0): (0, 'R', 23),
    (7, 1): (1, 'R', 23),
    (23, 0): (0, 'R', 23),
    (23, 1): (1, 'R', 8),      # first token of E; state 8 starts after it
    # E forward scan: zero-run counter; four zeros = field end
    (8, 0): (0, 'R', 9),
    (8, 1): (1, 'R', 8),
    (9, 0): (0, 'R', 10),
    (9, 1): (1, 'R', 8),
    (10, 0): (0, 'R', 11),
    (10, 1): (1, 'R', 8),
    (11, 0): (0, 'L', 12),      # fourth zero
    (11, 1): (1, 'R', 8),       # three-zero separator, resume
    # backward scan to the last separator
    (12, 0): (0, 'L', 12),
    (12, 1): (1, 'L', 13),
    (13, 1): (1, 'L', 13),
    (13, 0): (0, 'L', 14),
    (14, 1): (1, 'L', 13),
    (14, 0): (0, 'L', 15),
    (15, 1): (1, 'L', 13),
    (15, 0): (0, 'R', 16),      # third zero: first cell of the separator
    # zero from the separator to the field end
    (16, 0): (0, 'R', 17),      # separator zero 1
    (16, 1): (0, 'R', 17),
    (17, 0): (0, 'R', 18),      # separator zero 2
    (17, 1): (0, 'R', 18),
    (18, 0): (0, 'R', 19),      # separator zero 3
    (18, 1): (0, 'R', 19),
    (19, 0): (0, 'R', 20),
    (19, 1): (0, 'R', 19),
    (20, 0): (0, 'R', 21),
    (20, 1): (0, 'R', 19),
    (21, 0): (0, 'R', 22),
    (21, 1): (0, 'R', 19),
    (22, 0): (0, 'R', None),    # fourth zero of field marker; halt after move
    # (22, 1) deliberately absent: the field marker must be four zeros.
}


def run(tape, head, max_steps=100_000):
    m = TM(24, TABLE)
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


def check(n_terms=200):
    rng = random.Random(31)

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

    terms = [add(ONE, ONE), add(phi(0, ONE), phi(0, ONE)),
             add(B.epsilon0(), B.epsilon0()), add(B.epsilon1(), B.epsilon1()),
             add(add(ONE, ONE), ONE)]
    while len(terms) < n_terms + 5:
        base = term(2)
        v = add(base, base)
        if len(v.terms) >= 2 and v.terms[-1] == v.terms[-2]:
            terms.append(v)
    bad = 0
    for idx, v in enumerate(terms):
        if len(v.terms) < 2 or v.terms[-1] != v.terms[-2]:
            bad += 1
            print(f'  BAD TEST TERM {idx}: {v!r}')
            continue
        tape_s = term_tape(v)
        tape = {i: int(c) for i, c in enumerate(tape_s)}
        h_start = T.header_scan(tape_s)[-1][2]
        ok, out, head, state, steps = run(tape, h_start)
        if not ok:
            bad += 1
            print(f'  NO HALT term {idx}: {v!r}')
            continue
        got = T.from_tape(tape_string(out))
        want = B.pred(v)
        if got != want:
            bad += 1
            print(f'  PRED FAIL term {idx}: {v!r}')
            print(f'    got  {got!r}')
            print(f'    want {want!r}')
    print(f'  {len(terms)} duplicate-tail terms: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    v = add(add(ONE, ONE), ONE)
    print('example: predecessor of 3')
    print(f'  term   {v!r}')
    print(f'  tape   {term_tape(v)}')
    tape = {i: int(c) for i, c in enumerate(term_tape(v))}
    h_start = T.header_scan(term_tape(v))[-1][2]
    ok, out, head, state, steps = run(tape, h_start)
    s = tape_string(out)
    print(f'  out    {s}')
    print(f'  decoded {T.from_tape(s)!r}  (want {B.pred(v)!r})')
    print(f'  halted={ok} state={state} head={head} steps={steps}')


def main():
    ok = check()
    if ok:
        print()
        example()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
