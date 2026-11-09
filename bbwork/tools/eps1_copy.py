"""The eps_1 copy, built against the geometry a real run actually reaches.

`eps1_machine.py` stops at COPY with the head **on the wall** (not one cell
right of it) and the tape

    [block region: empty, blanks left of the wall] 1(wall) 0^k 1^v 0 1(seed)

(measured: wall=4/5/6, the value starting at 13/14/275 for v=2,7,255).  This
module tests the copy in isolation on that tape, before anything is spliced back
into eps_0's table.

## What the copy must produce

    block region: 1^v, right end flush against the blank at wall-1
    value region: 1^v, unchanged
    seed:         untouched

so the stage branch can spend the block (one mark per stage) while the value
stays available for the next rung.

## One sweep, not two

Copying is what eps_0 never needs, and with two symbols the only way is to write
*two* marks for every one read: one into the block (left of the wall, growing
leftwards) and one back into the value region.  One sweep does both, so there is
no second pass and no return move.

The value is drained from its **left** end, so "does the source continue?" is
the cell immediately right of the cell just erased -- local, which is all two
symbols give.  Each trip, with x the source's leftmost mark:

    1. erase x, step right (head at x+1)
    2. go left two cells and write the value's mark at x-1
       (x-1 was erased one trip earlier, so it is blank; on the first trip it is
        the blank in front of the old value)
    3. continue left over the copy, across the gap, over the wall, to the first
       blank left of the block, and write the block's mark there
    4. keep going left and carry the rung budget's rightmost mark to its left
       end, so the budget is pushed exactly one cell per block mark (see below)
    5. come back right: over the budget, the gap, the block, the wall, the gap,
       the copy, then one blank, and look at the next cell
           mark  -> the source continues: erase it and trip again
           blank -> the source is empty: done

The copy ends at [a-1 .. a+v-2], one blank left of where the value started, so
the seed never moves and the value keeps one blank between it and the block.
Cost is 2v^2 + 21v + 9 steps plus the budget carry.

## Why the rung budget is moved

The budget (how many rungs are left) cannot live to the right of the seed: the
rounds rewrite the value one cell right per round, so the seed drifts right by
about v per stage (measured: a=1 n=2 v=2 ends with the value at 275 and the seed
at 531, having started at 8 and 11).  Any mark parked beyond the seed gets
eaten by that drift, and a mark placed just past it breaks the rounds outright
(a 3-blank buffer with the budget beyond it stops the run at A7 after 41 steps
instead of reaching COPY at 140).

So the budget lives to the **left** of the stage block, and the block grows
leftwards, which means the budget has to recede.  Step 4 recedes it by exactly
one cell per block mark, which is exactly the growth rate, so the gap between
the block's left end and the budget's right end is the same at every trip and
at every rung.  The carry is "erase the budget's rightmost mark, walk to its
left end, write it there", which keeps the budget contiguous and moves it left
as a block.  A sentinel beyond it (never spent) is what stops a leftward walk
when the budget is empty: with two symbols "no marks left" is not visible.

That is the whole outer placement: `[sentinel][gap][1^a budget][gap][block] 0
1(wall) [value] 0 1(seed)`, and nothing in the copy ever walks past the seed.
"""

import sys

sys.path.insert(0, 'tools')
import tm

# --- states -----------------------------------------------------------------
ENTRY = 0       # on the wall, reading 1 (the state eps_0 hands over)
WALK = 1        # first trip: right over the gap to the value's left end
C1, C2, C3 = 2, 3, 4        # step left, then write the value's mark at x-1
CL = 5          # left over the copy
CG = 6          # left over the gap to the wall
B1 = 7          # left of the wall (blank at wall-1)
B2 = 8          # at wall-2: first block mark, or walk over the block
BL = 9          # left over the block to its left end
P1, P2 = 10, 11                             # carry the budget's rightmost mark
P3, P4, P5 = 12, 13, 14                     # back over the budget and the block
BQ = 15         # blank right of the block, at wall-1
BW = 16         # on the wall, crossing right
R1 = 17         # right over the gap
R2 = 18         # right over the copy
R3 = 19         # one blank past the copy: the source's left end, or nothing
DONE = 20

NAMES = {ENTRY: 'ENTRY', WALK: 'WALK', C1: 'C1', C2: 'C2', C3: 'C3', CL: 'CL',
         CG: 'CG', B1: 'B1', B2: 'B2', BL: 'BL', P1: 'P1', P2: 'P2',
         P3: 'P3', P4: 'P4', P5: 'P5', BQ: 'BQ', BW: 'BW',
         R1: 'R1', R2: 'R2', R3: 'R3'}

TABLE = {
    (ENTRY, 1): (1, 'R', WALK),
    # --- first trip: walk right to the value's left end and erase it
    (WALK, 0): (0, 'R', WALK),
    (WALK, 1): (0, 'R', C1),
    # --- step left over the erased cell and write the value's mark at x-1
    (C1, 1): (1, 'L', C2),
    (C1, 0): (0, 'L', C2),
    (C2, 0): (0, 'L', C3),
    (C2, 1): (1, 'L', C3),
    (C3, 0): (1, 'L', CL),
    (C3, 1): (1, 'L', CL),
    # --- left over the copy, then the gap, then the wall
    (CL, 1): (1, 'L', CL),
    (CL, 0): (0, 'L', CG),
    (CG, 0): (0, 'L', CG),
    (CG, 1): (1, 'L', B1),
    # --- left of the wall: write the block's mark, flush at wall-2 first
    (B1, 0): (0, 'L', B2),
    (B1, 1): (1, 'L', B2),
    (B2, 0): (1, 'L', P1),          # first trip: block was empty, mark at wall-2
    (B2, 1): (1, 'L', BL),          # block exists: walk to its left end
    (BL, 1): (1, 'L', BL),
    (BL, 0): (1, 'L', P1),          # write the block's new left mark
    # --- carry the budget's rightmost mark to its left end (push one cell)
    (P1, 0): (0, 'L', P1),          # over the gap toward the budget
    (P1, 1): (0, 'L', P2),          # erase the budget's rightmost mark
    (P2, 1): (1, 'L', P2),          # over the remaining budget marks
    (P2, 0): (1, 'R', P3),          # write it at the budget's left end
    (P3, 1): (1, 'R', P3),
    (P3, 0): (0, 'R', P4),          # the blank right of the budget
    (P4, 0): (0, 'R', P4),          # the gap
    (P4, 1): (1, 'R', P5),          # the block's left end
    (P5, 1): (1, 'R', P5),
    (P5, 0): (0, 'R', BQ),          # the blank right of the block (wall-1)
    (BQ, 0): (0, 'R', BW),
    (BQ, 1): (1, 'R', BW),
    (BW, 1): (1, 'R', R1),          # cross the wall, on the way back
    (BW, 0): (0, 'R', R1),
    # --- back over the gap and the copy, to one blank past the copy
    (R1, 0): (0, 'R', R1),
    (R1, 1): (1, 'R', R2),
    (R2, 1): (1, 'R', R2),
    (R2, 0): (0, 'R', R3),
    (R3, 1): (0, 'R', C1),
    # (R3, 0) absent: the source is empty, the copy is complete
}


def machine():
    return tm.TM(DONE + 1, TABLE)


def start_copy(v, budget=1, wall=10, gap_block=2, gap=8):
    """The tape a real run reaches at COPY, with the rung budget in place.

        [1^budget] [gap_block] [block: empty] 1(wall) 0^gap 1^v 0 1(seed)

    The budget is one contiguous run: it holds `budget` marks and is pushed left
    one cell per block mark, so its right end is always `gap_block` cells left of
    where the block's left end will be.  No separate sentinel is needed -- the
    run's own last mark is what tells the rung branch that no rung is left.
    """
    tape = {wall: 1}
    a = wall + gap                      # the value's start
    for i in range(v):
        tape[a + i] = 1
    tape[a + v] = 0
    seed = a + v + 1
    tape[seed] = 1
    right = wall - 3 - gap_block        # the budget's right end
    counts = list(range(right - budget + 1, right + 1))
    for p in counts:
        tape[p] = 1
    return tape, wall, ENTRY, dict(wall=wall, a=a, seed=seed, counts=counts)


def parts(tape, wall, grey):
    """Split the marks left of the wall into (budget run, block).

    The layout is [1^budget][gap][block] 1(wall): the block is the run flush
    against the wall, the budget is everything left of the gap.
    """
    left = sorted(p for p, x in tape.items() if x == 1 and p < wall)
    block = []
    p = wall - 2
    while p in left:
        block.append(p)
        p -= 1
    block.reverse()
    budget = [p for p in left if p not in block]
    return {'budget': budget, 'block': block}


def check(v, budget=1, gap_block=2, gap=8):
    tape, head, st, grey = start_copy(v, budget, gap_block=gap_block, gap=gap)
    wall, a, seed = grey['wall'], grey['a'], grey['seed']
    steps, t2, h2, s2, halted = machine().run(head=head, state=st, tape=tape,
                                             max_steps=200_000_000)
    got = parts(t2, wall, grey)
    value = sorted(p for p, x in t2.items() if x == 1 and wall < p <= seed)
    # the block: v marks flush at wall-2, growing left
    want_block = list(range(wall - 1 - v, wall - 1))
    # the value: v marks ending one cell left of where it started, seed kept
    want_value = list(range(a - 1, a - 1 + v)) + [seed]
    ok = (halted
          and got['block'] == want_block
          and value == want_value
          and len(got['budget']) == budget            # pushed, never eaten
          and got['budget'] == list(range(got['budget'][0],
                                          got['budget'][0] + budget))
          and all(t2.get(p, 0) == 1 for p in want_block + want_value)
          # the budget ends v cells left of where it started (one push a trip),
          # and the gap to the block never closes
          and got['budget'][-1] == grey['counts'][-1] - v
          and got['block'][0] - got['budget'][-1] >= 2)
    return ok, steps, got, value


def main():
    print('eps_1 copy: 1^v into the block, budget pushed left, value and seed kept')
    bad = 0
    cases = [(1, 1), (2, 1), (3, 1), (4, 1), (8, 1), (12, 1), (20, 1),
             (2, 2), (5, 3), (7, 5), (3, 9), (40, 4), (255, 1)]
    for v, budget in cases:
        ok, steps, got, value = check(v, budget)
        print(f'  v={v:<4} budget={budget:<3} steps={steps:<9} '
              f'block={len(got["block"]):<4} budget={len(got["budget"]):<3} '
              f'value={len(value) - 1:<4} {"PASS" if ok else "FAIL"}')
        if not ok:
            print(f'      got block={got["block"][:5]}.. budget={got["budget"][:5]}'
                  f' value={value[:5]}.. sentinel={got["sentinel"]}')
            bad += 1
    print('  gap block->budget (must not depend on v):')
    for v, budget in [(1, 1), (5, 1), (13, 1), (13, 2)]:
        ok, _, got, _ = check(v, budget)
        if got['block'] and got['budget']:
            print(f'    v={v:<3} budget={budget} gap='
                  f'{got["block"][0] - got["budget"][-1] - 1}')
    print('ALL OK' if not bad else f'{bad} FAILURES')
    return 0 if not bad else 1


if __name__ == '__main__':
    if '--trace' in sys.argv:
        i = sys.argv.index('--trace')
        v = int(sys.argv[i + 1]) if len(sys.argv) > i + 1 else 2
        tape, head, st, grey = start_copy(v, 2)
        m = machine()
        print('start', tm.tape_str(tape, head))
        prev = st
        for step in range(1, 400000):
            r = m.step(tape, head, st)
            if r is None:
                print(f'{step:>7} STOP {tm.tape_str(tape, head)}')
                break
            head, st = r
            if st != prev:
                print(f'{step:>7} {NAMES.get(st, st):>5} {tm.tape_str(tape, head)}')
                prev = st
    else:
        sys.exit(main())
