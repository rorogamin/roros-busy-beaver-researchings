"""The eps_1 machine: eps_0's rounds, with the stage count read off the value.

    stage branch (eps_0's table, one block mark per round)
      -> rung branch (spend a budget mark; halt when the budget is empty)
        -> copy (rebuild the block from the value, pushing the budget left)
          -> back into a round

which is the ladder `lvl 0 v = v`, `lvl (S k) v = run (lvl k v) v`: each rung
hands the next its own output as the stage count.

## Frame

    1^{a+1}(budget) 0^k [block] 1(wall) 0^k 1^v 0 1(seed)

with the head on the wall at the start.  The budget is a single run whose last
mark is the "no rungs left" signal, so spending one and testing the cell left of
it is local; a+1 marks give exactly a rungs.  The block is spent from its left
(eps_0's S0/S1/S2: S0 stops at the first blank left of the block, S1 erases the
leftmost, S2 asks whether a mark is left to its right), so the block stays flush
against the wall and the copy can grow it leftwards.

## Why the copy exists, and why it is one sweep

eps_0 takes its stage count as data.  For the value to decide the stage count, a
block of the value's length has to be laid down *while the value survives*; every
block operation eps_0 has consumes its source.  Two symbols give no delimiter, so
the drain has to be from the value's left end (the continuation test is the cell
right of the one just erased) and each trip writes two marks: one into the block,
one back into the value region.  `tools/eps1_copy.py` builds and tests that sweep
on its own; it is 16 states, costs 2v^2 + 35v + 9 at budget 1, and leaves the
value one cell left of where it started, so the seed never moves.

## Where the budget lives, and why

Right of the seed is unusable: the rounds rewrite the value one cell right per
round, so the seed drifts right by about v per stage (a 3-blank buffer with the
budget beyond it stops eps_0 at A7 after 41 steps instead of reaching the copy at
140).  So the budget sits left of the block, and the copy pushes it one cell per
block mark -- the same rate the block grows, which keeps the gap between them
constant.  Measured: v=1..255 with budgets 1..9, gap always 3 cells.

## What is checked, and what is not

The machine is 57 states and 100 rows (61 and 106 before the four exact
duplicates are merged; partition refinement finds R0/AA, R6/K1, S4/ZE, B2/BL, and
the checked runs take the same step counts either way).

`check` runs the ladder for a = 0 and a = 1 and compares with `lvl`: 3 for
(1,1) in 105 steps, 255 for (1,2) in 68384 steps, and the value unchanged for
a = 0.  a >= 2 is beyond simulation, not merely slow: lvl 2 1 = 65535 forces a
round over 65535 marks, about 4e9 steps.

Nothing here is a proof, and nothing here is a claim about f_eps_1.  The value
level is specified and proved in `rocq/Eps1Ladder.v`.  At the tape level the
rung branch -- ENTRY over the gap to the copy's entry, one budget mark spent,
block flush, value untouched -- is proved for every gap, budget and v in
`rocq/Eps1Tape.v`.  The copy sweep below it is proved through `sweep` in
`rocq/Eps1Copy.v`; the stage branch's decision -- block spent, hand over to the
rung branch -- is proved and composed into the copy (`block_spent_reaches_copy`
in `rocq/Eps1Tape.v`), while the branch's interior, its rounds, is still this
simulation (the statement it owes is step 3d of FGH_MACHINES_PLAN.md).  The
machine's run is finite because the budget is finite, and its cost per rung is
the copy's O(v^2) plus eps_0's rounds.
"""

import sys

sys.path.insert(0, 'tools')
import tm
import eps1_copy as cp

# --- eps_0's states, unchanged in meaning ------------------------------------
R0, R1, R2, R4, R5, R6 = range(6)
A5, A6, A7, A8, A9, AA = range(6, 12)
F0, F1, F2, F3, F4, F5 = range(12, 18)
P0, P1, P2 = range(18, 21)
S0, S1, S2, S3, S4 = range(21, 26)
K1, K2, K3, K4, K5, K6, K7 = range(26, 33)

# --- where the second feedback lives ----------------------------------------
# The copy's states are `eps1_copy`'s, laid out after eps_0's 33.  The machine is
#   stage branch (eps_0, spends one block mark per round)
#     -> rung branch (spend one budget mark; halt when the budget is empty)
#       -> copy (rebuild the block from the value, push the budget left)
#         -> back to the stage branch
# which is `lvl 0 v = v`, `lvl (S k) v = run (lvl k v) v`.
OFF = 33                        # the copy's states start here
ENTRY = OFF + cp.ENTRY        # on the wall: the rung branch starts here
WALK = OFF + cp.WALK
R3 = OFF + cp.R3              # copy done: hand over to the stage branch
G1, G2, G3 = 56, 57, 58         # spend a budget mark, or halt
E0 = 59                         # back on the wall: start the copy
ZA, ZB, ZC, ZD, ZE = 60, 61, 62, 63, 64   # handover: value -> the wall
NSTATES = 65

# eps_0's table, with the two halting rows of the stage branch redirected.
EPS0_ROWS = {
    (R0, 0): (0, 'L', R0),
    (R0, 1): (1, 'L', R1),
    (R1, 1): (1, 'R', R2),
    (R1, 0): (0, 'L', S0),
    (R2, 1): (0, 'R', R4),
    (R4, 0): (0, 'R', R4),
    (R4, 1): (1, 'R', R5),
    (R5, 1): (1, 'R', R5),
    (R5, 0): (0, 'L', R6),
    (R6, 1): (1, 'R', K2),
    (K1, 1): (1, 'R', K2),
    (K2, 0): (0, 'R', K2),
    (K2, 1): (1, 'R', K3),
    (K3, 0): (1, 'R', K4),
    (K3, 1): (1, 'R', K3),
    (K4, 0): (1, 'L', K5),
    (K5, 0): (0, 'L', K6),
    (K5, 1): (1, 'L', K5),
    (K6, 0): (0, 'L', K6),
    (K6, 1): (0, 'L', K7),
    (K7, 1): (1, 'R', K2),
    (K7, 0): (0, 'R', A5),
    (A5, 0): (0, 'R', A5),
    (A5, 1): (1, 'R', A6),
    (A6, 1): (1, 'R', A6),
    (A6, 0): (0, 'R', A7),
    (A7, 0): (1, 'L', A8),
    (A8, 0): (0, 'L', A9),
    (A9, 1): (1, 'L', A9),
    (A9, 0): (0, 'L', AA),
    (AA, 0): (0, 'L', AA),
    (AA, 1): (1, 'L', R1),
    (F0, 0): (0, 'R', F0),
    (F0, 1): (0, 'R', F1),
    (F1, 1): (1, 'L', F2),
    (F1, 0): (0, 'L', F3),
    (F2, 0): (0, 'L', F2),
    (F2, 1): (1, 'R', F4),
    (F3, 0): (0, 'L', F3),
    (F3, 1): (1, 'R', F5),
    (F4, 0): (1, 'R', F0),
    (F5, 0): (1, 'R', P0),
    (P0, 0): (0, 'R', P0),
    (P0, 1): (1, 'L', P1),
    (P1, 0): (0, 'L', P2),
    (P2, 0): (1, 'L', R0),
    (S0, 1): (1, 'L', S0),
    (S0, 0): (0, 'R', S1),
    (S1, 1): (0, 'R', S2),
    # eps_0 halts on both of these: the stage block is empty.  eps_1 copies the
    # value's length into the block here.  The copy rows are the missing half.
    (S1, 0): (0, 'R', ENTRY),       # block empty before a stage: treat as spent
    (S2, 1): (1, 'R', S3),          # more stages remain
    (S2, 0): (0, 'R', ENTRY),       # spent: hand over to the rung branch
    (S3, 1): (1, 'R', S3),
    (S3, 0): (0, 'R', S4),
    (S4, 1): (1, 'R', F0),
}

TABLE = dict(EPS0_ROWS)

# the copy's rows, renumbered; its ENTRY row is replaced by the rung branch and
# its R3-blank row by the handover
for _k, _v in cp.TABLE.items():
    _s, _r = _k
    if _s == cp.ENTRY:
        continue
    TABLE[(_s + OFF, _r)] = (_v[0], _v[1], None if _v[2] is None else _v[2] + OFF)

TABLE.update({
    # --- rung branch: spend one budget mark, or halt with the value
    (ENTRY, 1): (1, 'L', G1),       # off the wall, then left to the budget
    (G1, 0): (0, 'L', G1),
    (G1, 1): (0, 'L', G2),          # erase the budget's rightmost mark
    (G2, 1): (1, 'R', G3),          # a rung is available
    # (G2, 0) absent: the budget is spent, so the machine halts
    (G3, 0): (0, 'R', G3),          # back over the empty block region
    (G3, 1): (1, 'R', WALK),        # the wall, then the copy's first trip
    # --- handover: value -> gap -> wall -> wall-1 -> the block's right end
    (R3, 0): (0, 'L', ZA),
    (ZA, 0): (0, 'L', ZB),
    (ZB, 1): (1, 'L', ZB),          # over the new value
    (ZB, 0): (0, 'L', ZC),
    (ZC, 0): (0, 'L', ZC),          # over the gap
    (ZC, 1): (1, 'L', ZD),          # the wall
    (ZD, 0): (0, 'R', ZE),          # back over the wall
    (ZE, 1): (1, 'R', F0),          # wall+1, where a round starts
})

# --- exact merges -----------------------------------------------------------
# These four pairs have identical rows once their own targets are merged (found
# by partition refinement, not by eye), so redirecting into one representative
# leaves the machine's behaviour unchanged and drops four states.  R0/AA and
# R6/K1 are redundancy inherited from eps_0's table, S4/ZE and B2/BL from the
# splice.  Starting count 61, after this 57.
MERGE = {AA: R0, K1: R6, ZE: S4, cp.BL + OFF: cp.B2 + OFF}
TABLE = {_k: (_w, _d, MERGE.get(_t, _t)) for _k, (_w, _d, _t) in TABLE.items()
         if _k[0] not in MERGE}
STATES = sorted({_s for _s, _ in TABLE})

NAMES = {}
for _grp, _names in (
        ((R0, R1, R2, R4, R5, R6), ('R0', 'R1', 'R2', 'R4', 'R5', 'R6')),
        ((A5, A6, A7, A8, A9, AA), ('A5', 'A6', 'A7', 'A8', 'A9', 'AA')),
        ((F0, F1, F2, F3, F4, F5), ('F0', 'F1', 'F2', 'F3', 'F4', 'F5')),
        ((P0, P1, P2), ('P0', 'P1', 'P2')),
        ((S0, S1, S2, S3, S4), ('S0', 'S1', 'S2', 'S3', 'S4')),
        ((K1, K2, K3, K4, K5, K6, K7),
         ('K1', 'K2', 'K3', 'K4', 'K5', 'K6', 'K7'))):
    for _s, _n in zip(_grp, _names):
        if _s in MERGE:
            continue
        NAMES[_s] = _n
for _k, _n in cp.NAMES.items():
    NAMES[_k + OFF] = _n
NAMES.update({ENTRY: 'ENTRY', G1: 'G1', G2: 'G2', G3: 'G3', E0: 'E0',
              ZA: 'ZA', ZB: 'ZB', ZC: 'ZC', ZD: 'ZD', ZE: 'ZE'})


def machine():
    return tm.TM(NSTATES, TABLE)


def stage(v):
    """One eps_0 round."""
    return 2 ** (v + 1) - 1


def run(n, v):
    for _ in range(n):
        v = stage(v)
    return v


def lvl(k, v):
    """The ladder: each rung hands the next its own output as the stage count."""
    c = v
    for _ in range(k):
        c = run(c, v)
    return c


def start(a, v, wall=10, gap_val=3, gap_block=2):
    """The machine's input tape.

        1^{a+1}(budget) 0^k [block region: empty] 1(wall)
        0^{gap_val-1} 1^v 0 1(seed)

    `a` is how many rungs to run.  The block region starts empty: every rung
    begins with the budget check and then the copy, so the input is the budget
    and the value, and `a = 0` halts at once with the value (lvl 0 v = v).
    """
    tape = {}
    tape[wall] = 1
    base = wall + gap_val
    for i in range(v):
        tape[base + i] = 1
    tape[base + v] = 0
    seed = base + v + 1
    tape[seed] = 1
    # the budget is one run of a+1 marks: the rung branch spends one and then
    # runs a rung while a mark is left, so a+1 marks give exactly a rungs and
    # the last mark is the "no rungs left" signal (no separate sentinel).
    right = wall - 3 - gap_block
    counts = list(range(right - a, right + 1))
    for p in counts:
        tape[p] = 1
    return tape, wall, ENTRY, dict(wall=wall, base=base, seed=seed,
                                   counts=counts, block_lo=wall - 2)


def value(tape, wall):
    """The value: the marks right of the wall, minus the seed.

    The seed is rewritten at a new position each round, so it is counted, not
    located: right of the wall there are exactly the value's marks and the seed.
    """
    return sum(1 for p, x in tape.items() if wall < p and x == 1) - 1


def render(tape, head, pad=2):
    if not tape:
        return '[blank]'
    lo = min(min(tape), head) - pad
    hi = max(max(tape), head) + pad
    return ''.join('<' + str(tape.get(i, 0)) + '>' if i == head
                   else str(tape.get(i, 0)) for i in range(lo, hi + 1))


def check():
    """Run the machine on (rungs, value) and compare with the ladder."""
    print(f'eps_1 machine: {len(STATES)} states, {len(TABLE)} rows; '
          'lvl k v where each rung hands the next its own output')
    # a >= 2 is out of reach here, not untested-by-laziness: lvl 2 1 = 65535
    # already forces a round over 65535 marks (~4e9 steps).
    cases = [(0, 1), (0, 2), (0, 5), (1, 1), (1, 2)]
    ok = True
    for a, v in cases:
        tape, head, st, grey = start(a, v)
        m = machine()
        steps, t2, h2, s2, halted = m.run(head=head, state=st, tape=tape,
                                          max_steps=20_000_000)
        want = lvl(a, v)
        got = value(t2, grey['wall'])
        budget_left = sum(1 for p in grey['counts'] if t2.get(p, 0) == 1)
        good = halted and got == want and budget_left == 0
        ok = ok and good
        print(f'  rungs={a} v={v}: steps={steps} stop={NAMES.get(s2, s2)} '
              f'value={got} want={want} budget_left={budget_left} '
              f'{"PASS" if good else "FAIL"}')
        if not good:
            print('      tape', render(t2, h2))
    return ok


if __name__ == '__main__':
    if '--trace' in sys.argv:
        args = [int(x) for x in sys.argv[sys.argv.index('--trace') + 1:]][:2]
        trace(*(args or [1, 1]))
    else:
        ok = check()
        print('ALL OK' if ok else 'FAILURES')
        sys.exit(0 if ok else 1)
