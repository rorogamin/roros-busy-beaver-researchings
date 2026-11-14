"""A real 5-tuple FS arm for the simplest exponent case: omega[1] = 2.

Input:  the one-header term phi_0(1) = omega, with the canonical empty work
        and index fields.
Output: 1 + 1, i.e. two phi_0(0) headers and two zero exponents.

The table is a fixed-case recognizer/writer.  It checks every cell of the
28-cell input tape and writes the 40-cell output tape.  It is deliberately
narrow: it is the first concrete FS arm, not a general FS implementation.

Run: python tools/bve_fs_simple.py
"""

import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import ONE, phi, add
import bve_two_bank as T
from tm import TM

SIMPLE = phi(0, ONE)
N = 1

# FIELD + H + DELIM + E + FIELD + empty work/index fields
INPUT = '0000011010001011000000000000'

# FIELD + (two headers) + DELIM + (two zero exponents) + trailing fields
OUTPUT = '0000011011110100010010001001000000000000'

WIDTH = max(len(INPUT), len(OUTPUT))
N_STATES = WIDTH + 1


def build_table():
    rows = {}
    for pos in range(WIDTH):
        expect = int(INPUT[pos]) if pos < len(INPUT) else 0
        write = int(OUTPUT[pos]) if pos < len(OUTPUT) else 0
        rows[(pos, expect)] = (write, 'R', pos + 1)
    return rows


TABLE = build_table()


def run(tape, head=0, max_steps=10_000):
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


def check():
    bad = 0

    if T.to_tape(SIMPLE) != INPUT:
        bad += 1
        print(f'  INPUT CONSTANT FAIL: {T.to_tape(SIMPLE)!r}')
    if T.to_tape(B.model_fs(SIMPLE, N)) != OUTPUT:
        bad += 1
        print(f'  OUTPUT CONSTANT FAIL: {T.to_tape(B.model_fs(SIMPLE, N))!r}')

    cells = {i: int(c) for i, c in enumerate(INPUT)}
    ok, out, head, state, steps = run(cells)
    got = tape_string(out)
    if not ok:
        bad += 1
        print('  NO HALT')
    elif got != OUTPUT:
        bad += 1
        print(f'  TABLE FAIL: {got!r} != {OUTPUT!r}')
    else:
        decoded = T.from_tape(got)
        if decoded != B.model_fs(SIMPLE, N):
            bad += 1
            print(f'  DECODE FAIL: {decoded!r}')

    # A different term must not be silently accepted as the output.
    wrong = T.to_tape(ONE)
    ok2, out2, _h2, _s2, _p2 = run(
        {i: int(c) for i, c in enumerate(wrong)})
    if tape_string(out2) == OUTPUT:
        bad += 1
        print('  WRONG-INPUT ACCEPT FAIL')

    print(f'  {N_STATES} states, {len(TABLE)} rows; '
          f'{len(INPUT)} -> {len(OUTPUT)} cells: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    cells = {i: int(c) for i, c in enumerate(INPUT)}
    ok, out, head, state, steps = run(cells)
    print('example: omega[1] = 2')
    print(f'  in   {INPUT}')
    print(f'  out  {tape_string(out)}')
    print(f'  term {T.from_tape(tape_string(out))!r}')
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
