"""The eps_0 machine: 33 states, two symbols, one stage = one exponentiation.

Layout, canonical between stages:

    1^n  0  1(wall)  [1^c]  0  1^1  0  1(seed)
    stages  gap  wall  counter       new   seed

A stage does three things.

1. Fuel.  Every mark of the value is moved into the counter, one per trip:
   erase the value's *first* mark, carry it left, write it just right of the
   counter's last mark.  Taking from the front is what makes the move work in
   two symbols.  The test for "value exhausted" is the cell just right of the
   erased mark, which is inside the value: a mark means the value continues, a
   blank means it was the last one.  Taking from the tail instead does not work
   -- the cell left of the tail can be the counter once the counter has grown
   up against the value, and the drive then believes the value has marks it has
   already moved (that bug made the machine loop).

2. Rounds.  The counter now holds c = v marks, so the round engine runs c times;
   each round erases one counter mark and lets module K rebuild the value as
   `seed + 2 per source mark`.  Starting from a value of 1, that is
   `(1+1)*2^c - 1`.

3. Stage.  When the counter runs out, the left walk reaches the wall; the drive
   crosses the gap, erases one mark of the stage block, and starts over.  With
   no stage marks left it halts.

One stage maps `v -> 2^(v+1) - 1`, and n stages is the n-th rung of the tower:
`1 -> 3 -> 15 -> 255 -> 65535 -> ...`.  That is eps_0: the rounds of a stage are
the value the previous stage produced.

The stage count must come from the input.  A version that let the value decide
its own stage count does not halt -- each stage multiplies the value by about
`2^(v/2)`, so the next stage always has more rounds than the last.  See
`tools/eps0_fuel.py`.

States: 0..25 the drive, 26..32 module K.  33 total.
"""

import sys

sys.path.insert(0, 'tools')
import tm

# --- round entry and loop ---------------------------------------------------
R0, R1, R2, R4, R5, R6 = range(6)
# --- return after a round ---------------------------------------------------
A5, A6, A7, A8, A9, AA = range(6, 12)
# --- fuel: move the value, front first, into the counter --------------------
F0, F1, F2, F3, F4, F5 = range(12, 18)
# --- the new value after the fuel move --------------------------------------
P0, P1, P2 = range(18, 21)
# --- stage branch -----------------------------------------------------------
S0, S1, S2, S3, S4 = range(21, 26)
# --- module K ---------------------------------------------------------------
K1, K2, K3, K4, K5, K6, K7 = range(26, 33)

TABLE = {
    # -- round entry: walk left over blanks to the counter's last mark -------
    (R0, 0): (0, 'L', R0),
    (R0, 1): (1, 'L', R1),
    # the found mark: a mark to its left means counter, a blank the wall
    (R1, 1): (1, 'R', R2),          # another round: erase it
    (R1, 0): (0, 'L', S0),          # the wall: stage over, look at the block
    (R2, 1): (0, 'R', R4),          # spent a round
    (R4, 0): (0, 'R', R4),          # over the hole and the gap
    (R4, 1): (1, 'R', R5),          # the value's first mark
    (R5, 1): (1, 'R', R5),          # over the value
    (R5, 0): (0, 'L', R6),          # back onto its last mark
    (R6, 1): (1, 'R', K2),          # hand to K
    # -- module K -----------------------------------------------------------
    (K1, 1): (1, 'R', K2),
    (K2, 0): (0, 'R', K2),          # over the gap to the destination's seed
    (K2, 1): (1, 'R', K3),
    (K3, 0): (1, 'R', K4),          # append a destination mark
    (K3, 1): (1, 'R', K3),
    (K4, 0): (1, 'L', K5),
    (K5, 0): (0, 'L', K6),
    (K5, 1): (1, 'L', K5),
    (K6, 0): (0, 'L', K6),
    (K6, 1): (0, 'L', K7),          # erase a source mark
    (K7, 1): (1, 'R', K2),          # source continues
    # -- return after a round ----------------------------------------------
    (K7, 0): (0, 'R', A5),
    (A5, 0): (0, 'R', A5),          # blanks before the new block
    (A5, 1): (1, 'R', A6),
    (A6, 1): (1, 'R', A6),          # over the new block
    (A6, 0): (0, 'R', A7),
    (A7, 0): (1, 'L', A8),          # the next seed, one blank past the block
    (A8, 0): (0, 'L', A9),          # back across that gap onto the block
    (A9, 1): (1, 'L', A9),          # back left over the block
    (A9, 0): (0, 'L', AA),
    (AA, 0): (0, 'L', AA),          # over the dead region
    (AA, 1): (1, 'L', R1),          # first mark: counter or wall
    # -- fuel move: take the value's first mark ------------------------------
    (F0, 0): (0, 'R', F0),          # blanks right of the counter
    (F0, 1): (0, 'R', F1),          # erase the first mark, then test right
    (F1, 1): (1, 'L', F2),          # value continues
    (F1, 0): (0, 'L', F3),          # that was the last mark
    (F2, 0): (0, 'L', F2),          # carry-more: over blanks to the counter
    (F2, 1): (1, 'R', F4),
    (F3, 0): (0, 'L', F3),          # carry-last
    (F3, 1): (1, 'R', F5),
    (F4, 0): (1, 'R', F0),          # write it, back for more
    (F5, 0): (1, 'R', P0),          # write it, then the new value
    # -- the new value, one gap left of the old seed -----------------------
    (P0, 0): (0, 'R', P0),          # blanks up to the old seed
    (P0, 1): (1, 'L', P1),          # keep the seed as the destination
    (P1, 0): (0, 'L', P2),
    (P2, 0): (1, 'L', R0),          # write the value, then the rounds begin
    # -- stage branch -------------------------------------------------------
    # The block's *right* end must stay flush with the gap, or the next walk
    # finds a hole instead of a mark -- that is what made this branch halt
    # after two stages whatever the block's length.  So the stage is spent
    # from the block's left end, which leaves its holes on the outside.
    (S0, 1): (1, 'L', S0),          # a stage mark: walk left over the block
    (S0, 0): (0, 'R', S1),          # its left end: back onto the leftmost mark
    (S1, 1): (0, 'R', S2),          # spend it; the cell right of it decides
    # (S1, 0) undefined: the block was already empty, halt
    (S2, 1): (1, 'R', S3),          # more stages remain
    # (S2, 0) undefined: the last stage was just spent, halt
    (S3, 1): (1, 'R', S3),          # walk right over what is left of the block
    (S3, 0): (0, 'R', S4),          # the gap
    (S4, 1): (1, 'R', F0),          # the wall, then fuel the next stage
}


def machine():
    return tm.TM(33, TABLE)


def start(n, v):
    """1^n 0 1(wall) 0 1^v 0 1(seed), head one right of the wall."""
    tape = {}
    for i in range(n):
        tape[i] = 1
    tape[n] = 0
    wall = n + 1
    tape[wall] = 1
    gap = wall + 1
    tape[gap] = 0
    base = gap + 1
    for i in range(v):
        tape[base + i] = 1
    tape[base + v] = 0
    tape[base + v + 1] = 1
    return tape, gap, F0


def value(tape, n):
    """Marks minus the wall, the stage block and the trailing seed."""
    total = sum(1 for x in tape.values() if x == 1)
    stages = sum(1 for p, x in tape.items() if p < n and x == 1)
    return total - 1 - stages - 1


def render(tape, head, pad=2):
    if not tape:
        return '[blank]'
    lo = min(min(tape), head) - pad
    hi = max(max(tape), head) + pad
    return ''.join('<' + str(tape.get(i, 0)) + '>' if i == head
                   else str(tape.get(i, 0)) for i in range(lo, hi + 1))


NAMES = {}
for _grp, _names in (
        ((R0, R1, R2, R4, R5, R6), ('R0', 'R1', 'R2', 'R4', 'R5', 'R6')),
        ((A5, A6, A7, A8, A9, AA), ('A5', 'A6', 'A7', 'A8', 'A9', 'AA')),
        ((F0, F1, F2, F3, F4, F5), ('F0', 'F1', 'F2', 'F3', 'F4', 'F5')),
        ((P0, P1, P2), ('P0', 'P1', 'P2')),
        ((S0, S1, S2, S3, S4), ('S0', 'S1', 'S2', 'S3', 'S4')),
        ((K1, K2, K3, K4, K5, K6, K7), ('K1', 'K2', 'K3', 'K4', 'K5', 'K6',
                                        'K7'))):
    for _s, _n in zip(_grp, _names):
        NAMES[_s] = _n


def trace(n, v, limit=20000):
    m = machine()
    tape, head, st = start(n, v)
    print(f'--- n={n} v={v}: {render(tape, head)}')
    prev = st
    for step in range(1, limit):
        r = m.step(tape, head, st)
        if r is None:
            print(f'  {step:>6} HALT {render(tape, head)}  '
                  f'value={value(tape, n)}')
            return tape, True
        head, st = r
        if st != prev:
            print(f'  {step:>6} {NAMES.get(st, st):>4} {render(tape, head)}')
            prev = st
    print('  no halt')
    return tape, False


def check():
    m = machine()
    cases = [(1, 1, 3), (1, 2, 7), (1, 3, 15), (2, 1, 15), (2, 2, 255)]
    ok = True
    for n, v, want in cases:
        tape, head, st = start(n, v)
        steps, tape2, head2, st2, halted = m.run(head=head, state=st, tape=tape,
                                                 max_steps=4000000)
        got = value(tape2, n)
        good = halted and got == want
        ok = ok and good
        print(f'  n={n} v={v}: steps={steps} halted={halted} '
              f'value={got} want={want} {"PASS" if good else "FAIL"}')
    return ok


if __name__ == '__main__':
    if '--trace' in sys.argv:
        a = [int(x) for x in sys.argv[sys.argv.index('--trace') + 1:]][:2]
        trace(*(a or [1, 1]))
    else:
        print('eps_0 machine: n stages of v -> 2^(v+1) - 1')
        ok = check()
        print('ALL OK' if ok else 'FAILURES')
        sys.exit(0 if ok else 1)
