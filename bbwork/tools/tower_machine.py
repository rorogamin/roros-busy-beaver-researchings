"""The tower machine: module K inside a drive that reads its round count off
the tape.

Layout at the top of a round:

    1(wall)  1^c  0  1^v  0  1^seed

One round consumes one c mark and replaces the value block by K's output, which
for a source of v marks is 1 + 2v marks: the seed plus two per source mark.
The drive then writes the seed for the *next* round one cell beyond the new
block, leaving a blank gap.  The gap matters: without it the next round's walk
runs straight over the seed and takes block+seed as its source, which silently
changes the recurrence from v -> 2v+1 to v -> 2v+3.  That bug is what the first
version of this drive did, and the trace showed it as a short count.

After c rounds the value is

    (v + 1) * 2^c - 1

and the tape carries the wall (never erased) plus one trailing seed written
after the last round, so `value()` subtracts both.

States 0..11 are the drive, 20..26 are module K's seven states.  K's halt
(K7 on a blank) is intercepted as the drive's return.

Return branch.  The walk back over the dead region stops at the first mark it
meets: either c's rightmost mark or the wall.  Since the wall is adjacent to the
c block, that mark has a mark to its left exactly when another round remains.
So DB tests the cell left of the found mark: a mark means erase it and go
again, a blank means the found mark is the wall and the machine halts.
"""

import sys

sys.path.insert(0, 'tools')
import tm

# --- drive states -----------------------------------------------------------
D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, DA, DB = range(12)
# --- module K, shifted ------------------------------------------------------
K1, K2, K3, K4, K5, K6, K7 = range(20, 27)

TABLE = {
    # erase the rightmost c mark and step back onto the hole
    (D0, 1): (0, 'L', D1),
    (D1, 1): (1, 'R', D2),
    # right over the dead region to the value block
    (D2, 0): (0, 'R', D2),
    (D2, 1): (1, 'R', D3),
    (D3, 1): (1, 'R', D3),      # over the value block
    (D3, 0): (0, 'L', D4),      # back onto its last mark
    (D4, 1): (1, 'R', K2),      # hand over to K
    # module K
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
    # K used to halt here: walk to the new block, then past it
    (K7, 0): (0, 'R', D5),
    (D5, 0): (0, 'R', D5),      # blanks after the old source
    (D5, 1): (1, 'R', D6),      # the new block's first mark
    (D6, 1): (1, 'R', D6),      # over the new block
    (D6, 0): (0, 'R', D7),      # into the blank gap
    (D7, 0): (1, 'L', D8),      # write the next seed beyond the gap
    (D8, 0): (0, 'L', D9),      # back onto the block's last mark
    (D9, 1): (1, 'L', D9),      # left over the new block
    (D9, 0): (0, 'L', DA),      # into the dead region
    (DA, 0): (0, 'L', DA),      # over the dead region
    (DA, 1): (1, 'L', DB),      # first mark: c's rightmost, or the wall
    (DB, 1): (1, 'R', D0),      # a mark to its left: another round
    # (DB, 0) undefined: the found mark is the wall, halt
}


def machine():
    return tm.TM(27, TABLE)


def start(c, v, seed=1):
    """1(wall) 1^c 0 1^v 0 1^seed, head on c's rightmost mark."""
    tape = {0: 1}
    for i in range(c):
        tape[1 + i] = 1
    tape[1 + c] = 0
    base = c + 2
    for i in range(v):
        tape[base + i] = 1
    tape[base + v] = 0
    for i in range(seed):
        tape[base + v + 1 + i] = 1
    return tape, c, D0


def value(tape):
    """Marks minus the wall and the trailing seed."""
    return sum(1 for v in tape.values() if v == 1) - 2


def label(s):
    names = {D0: 'D0', D1: 'D1', D2: 'D2', D3: 'D3', D4: 'D4', D5: 'D5',
             D6: 'D6', D7: 'D7', D8: 'D8', D9: 'D9', DA: 'DA', DB: 'DB'}
    names.update({K1: 'K1', K2: 'K2', K3: 'K3', K4: 'K4', K5: 'K5',
                  K6: 'K6', K7: 'K7'})
    return names.get(s, str(s))


def render(tape, head, pad=2):
    if not tape:
        return '[blank]'
    lo = min(min(tape), head) - pad
    hi = max(max(tape), head) + pad
    return ''.join('<' + str(tape.get(i, 0)) + '>' if i == head
                   else str(tape.get(i, 0)) for i in range(lo, hi + 1))


def trace(c, v, limit=4000):
    m = machine()
    tape, head, st = start(c, v)
    print(f'--- c={c} v={v}: {render(tape, head)}')
    prev = st
    for step in range(1, limit):
        r = m.step(tape, head, st)
        if r is None:
            print(f'  {step:>4} HALT  {render(tape, head)}  value={value(tape)}')
            return tape, True
        head, st = r
        if st != prev:
            print(f'  {step:>4} {label(st):>3}  {render(tape, head)}')
            prev = st
    print('  no halt')
    return tape, False


def check(c_max=3, v_max=3):
    m = machine()
    ok = True
    for c in range(1, c_max + 1):
        for v in range(1, v_max + 1):
            tape, head, st = start(c, v)
            steps, tape2, head2, st2, halted = m.run(head=head, state=st,
                                                     tape=tape, max_steps=500000)
            want = (v + 1) * 2 ** c - 1
            got = value(tape2)
            good = halted and got == want
            ok = ok and good
            print(f'  c={c} v={v}: steps={steps} halted={halted} '
                  f'marks={got} want={want} {"PASS" if good else "FAIL"}')
    return ok


if __name__ == '__main__':
    if '--trace' in sys.argv:
        trace(1, 1)
    else:
        print('tower machine: v -> (v+1)*2^c - 1 after c rounds')
        ok = check()
        print('ALL OK' if ok else 'FAILURES')
        sys.exit(0 if ok else 1)
