"""23-state composed cursor for the two-bank rBVE tape.

Entry contract
--------------
The composed table starts on the first zero of the H/E separator.  Its first
five states walk left to the duplicate-flag cell of the LAST header; the
remaining 18 states are the active-site cursor.  The tape is

    FIELD + H + DELIM + E + FIELD

with FIELD = 0000, DELIM = 000.  H is a run of five-cell headers
(flag + four-cell op); E is a run of postfix exponent blocks separated by
000, ending in the four-zero field marker.

Exit
----
The table halts on the first zero of the last 000 separator (the third zero
counted from the right).  The last exponent starts three cells to the right,
so the checker compares `head + 3` with `bve_two_bank.last_exponent`.  The
table passes through the flag-dispatch states and op-dispatch states, which
the checker records; this validates the read/dispatch path, not only the final
head position.

The 18-state core is still callable directly with entry at the last header;
`run_cursor` tests that contract, while `run_h_end` tests the composed 23-state
table.  This is a cursor table, not a full rewrite engine: it does not copy or
expand an exponent.
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_two_bank as T
from tm import TM

# States: 0 flag; 1/2 flag paths; 3/4 op bits; 5/6 op paths; 7-9 H separator;
# 10-13 forward E scan (zero-run counter); 14 skip field zeros; 15-17 backward
# three-zero detector.  State 17 on 0 is intentionally undefined (halt).
#
# (state, read) -> (write, direction, next)
TABLE = {
    (0, 0): (0, 'R', 1),
    (0, 1): (1, 'R', 2),
    (1, 1): (1, 'R', 3),
    (2, 1): (1, 'R', 3),
    (3, 1): (1, 'R', 4),
    (4, 0): (0, 'R', 5),       # phi_0
    (4, 1): (1, 'R', 6),       # phi_1 (preserve the op bit)
    (5, 0): (0, 'R', 7),
    (5, 1): (1, 'R', 7),
    (6, 0): (0, 'R', 7),
    (6, 1): (1, 'R', 7),
    (7, 0): (0, 'R', 8),       # H end, first zero
    (7, 1): (1, 'R', 8),
    (8, 0): (0, 'R', 9),       # second zero
    (8, 1): (1, 'R', 9),
    (9, 0): (0, 'R', 10),      # third zero; next cell is E
    (9, 1): (1, 'R', 10),
    (10, 0): (0, 'R', 11),     # first zero of a run
    (10, 1): (1, 'R', 10),
    (11, 0): (0, 'R', 12),     # second zero
    (11, 1): (1, 'R', 10),
    (12, 0): (0, 'R', 13),     # third zero
    (12, 1): (1, 'R', 10),
    (13, 0): (0, 'L', 14),     # fourth zero: field end, go back
    (13, 1): (1, 'R', 10),     # three-zero separator: resume at next cell
    (14, 0): (0, 'L', 14),     # skip field zeros
    (14, 1): (1, 'L', 15),     # last exponent's final token
    (15, 1): (1, 'L', 15),
    (15, 0): (0, 'L', 16),     # one zero
    (16, 1): (1, 'L', 15),
    (16, 0): (0, 'L', 17),     # two zeros
    (17, 1): (1, 'L', 15),
    # (17, 0) is omitted: halt on the third zero of the separator.
}


SHIFT = 5
TABLE_HEND = {}
for _s in range(SHIFT):
    for _r in (0, 1):
        TABLE_HEND[(_s, _r)] = (_r, 'L', _s + 1)
for (_s, _r), (_w, _d, _n) in TABLE.items():
    TABLE_HEND[(_s + SHIFT, _r)] = (
        _w, _d, None if _n is None else _n + SHIFT)


def run_cursor(tape, head, max_steps=100_000):
    """Run the table and return (halted, head, state, steps, visited)."""
    m = TM(18, TABLE)
    tape = dict(tape)
    state = 0
    visited = set()
    for steps in range(max_steps):
        visited.add(state)
        k = (state, tape.get(head, 0))
        if k not in TABLE:
            return True, head, state, steps, visited
        write, direction, nxt = TABLE[k]
        tape[head] = write
        head += 1 if direction == 'R' else -1
        state = nxt
    return False, head, state, max_steps, visited


def run_h_end(tape, head, max_steps=100_000):
    """Run the composed table from the first zero of the H/E separator."""
    m = TM(23, TABLE_HEND)
    tape = dict(tape)
    state = 0
    visited = set()
    for steps in range(max_steps):
        visited.add(state)
        k = (state, tape.get(head, 0))
        if k not in TABLE_HEND:
            return True, head, state, steps, visited
        write, direction, nxt = TABLE_HEND[k]
        tape[head] = write
        head += 1 if direction == 'R' else -1
        state = nxt
    return False, head, state, max_steps, visited


def term_tape(v):
    h, e = T.banks(v)
    if not h or h == T.TOK_ZERO:
        raise ValueError('zero term has no header')
    return T.FIELD + h + T.DELIM + e + T.FIELD


def check(n_terms=200):
    rng = random.Random(23)

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

    terms = [ONE, phi(0, ONE), phi(1, ZERO), add(phi(0, ONE), ONE),
             B.epsilon1(), add(ONE, ONE), add(phi(0, add(ONE, ONE)), ONE)]
    terms += [term(3) for _ in range(n_terms)]
    bad = 0
    for idx, v in enumerate(terms):
        try:
            tape_s = term_tape(v)
        except ValueError:
            continue
        tape = {i: int(c) for i, c in enumerate(tape_s)}
        hs = T.header_scan(tape_s)
        last_flag, last_op = hs[-1][1], hs[-1][0]
        h_start = hs[-1][2]
        exp_start = T.last_exponent(tape_s)[0]
        ok, head, state, steps, visited = run_cursor(tape, h_start)
        if not ok:
            bad += 1
            print(f'  NO HALT term {idx}: {v!r}')
            continue
        if state != 17 or head + 3 != exp_start:
            bad += 1
            print(f'  LOCATE FAIL term {idx}: {v!r}')
            print(f'    halt state {state}, head {head}, want exponent {exp_start}')
            continue
        want_flag_state = 2 if last_flag else 1
        want_op_state = 6 if last_op else 5
        if want_flag_state not in visited or want_op_state not in visited:
            bad += 1
            print(f'  DISPATCH FAIL term {idx}: {v!r}')
            print(f'    visited {sorted(visited)}, want {want_flag_state}/{want_op_state}')
            continue
    print(f'  {len(terms)} terms, {n_terms} random: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_h_end(n_terms=200):
    rng = random.Random(23)

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

    terms = [ONE, phi(0, ONE), phi(1, ZERO), add(phi(0, ONE), ONE),
             B.epsilon1(), add(ONE, ONE), add(phi(0, add(ONE, ONE)), ONE)]
    terms += [term(3) for _ in range(n_terms)]
    bad = 0
    for idx, v in enumerate(terms):
        try:
            tape_s = term_tape(v)
        except ValueError:
            continue
        tape = {i: int(c) for i, c in enumerate(tape_s)}
        hs = T.header_scan(tape_s)
        last_flag, last_op = hs[-1][1], hs[-1][0]
        exp_start = T.last_exponent(tape_s)[0]
        # The entry is the first cell of the H/E separator, not the header.
        h_end = T.FIELD.__len__() + len(T.banks(v)[0])
        ok, head, state, steps, visited = run_h_end(tape, h_end)
        if not ok:
            bad += 1
            print(f'  H-END NO HALT term {idx}: {v!r}')
            continue
        if state != 22 or head + 3 != exp_start:
            bad += 1
            print(f'  H-END LOCATE FAIL term {idx}: {v!r}')
            print(f'    halt state {state}, head {head}, want exponent {exp_start}')
            continue
        want_flag_state = 7 if last_flag else 6
        want_op_state = 11 if last_op else 10
        if want_flag_state not in visited or want_op_state not in visited:
            bad += 1
            print(f'  H-END DISPATCH FAIL term {idx}: {v!r}')
            print(f'    visited {sorted(visited)}, want {want_flag_state}/{want_op_state}')
            continue
    print(f'  H-end entry: {len(terms)} terms, {n_terms} random: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    v = add(phi(0, ONE), ONE)
    tape_s = term_tape(v)
    tape = {i: int(c) for i, c in enumerate(tape_s)}
    hs = T.header_scan(tape_s)
    exp_start = T.last_exponent(tape_s)[0]
    ok, head, state, steps, visited = run_cursor(tape, hs[-1][2])
    print('example: w + 1')
    print(f'  tape       {tape_s}')
    print(f'  headers    {hs}')
    print(f'  codec exp  {exp_start}')
    print(f'  cursor     halted={ok} state={state} head={head} '
          f'exp(head+3)={head + 3} steps={steps}')
    print(f'  visited    {sorted(visited)}')
    print()
    v = add(phi(0, ONE), ONE)
    tape_s = term_tape(v)
    tape = {i: int(c) for i, c in enumerate(tape_s)}
    h, _e = T.banks(v)
    h_end = len(T.FIELD) + len(h)
    exp_start = T.last_exponent(tape_s)[0]
    ok, head, state, steps, visited = run_h_end(tape, h_end)
    print('example: composed H-end entry')
    print(f'  codec exp  {exp_start}')
    print(f'  cursor     halted={ok} state={state} head={head} '
          f'exp(head+3)={head + 3} steps={steps}')
    print(f'  visited    {sorted(visited)}')


def main():
    ok = check()
    ok = check_h_end() and ok
    if ok:
        print()
        example()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
