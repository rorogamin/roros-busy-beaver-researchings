"""First module of our own eps-machine: the unary "append two per mark" engine.

Layout it operates on

    1^x 0 1        source block, one blank, a seeded destination of 1 mark

and it halts with

    0^x 0 1^(2x+1)   (source consumed, destination grown by two per source mark)

Why this module first: doubling (x -> 2x), copying (y -> y + x), and the
"re-read the block as a program" step are all this walk with a different append
count.  Getting it right once is what makes the eps-machine design more than a
diagram.

Order matters, and the first version of this table had it backwards: it erased a
source mark and *then* tested, so the last mark was destroyed without being
copied and every answer came out 2x-1.  The loop below appends first, then
erases, then tests.

    K1  at the source's rightmost mark: step into the hole
    K2  skip the accumulated blanks to the destination
    K3  walk over the destination to its right end
    K4  append the first new mark
    K5  append the second, turn back
    K6  walk left over the destination, then over the blanks
    K7  erase the source's rightmost mark; halt if it was the last one

The blank-skipping in K2/K6 is why the destination is seeded: with an empty
destination, "skip blanks" has no stopping point.  The seed costs one mark and
one bookkeeping step when the value is read back.
"""

import sys

sys.path.insert(0, 'tools')
import tm

TABLE = {
    ('K1', 1): (1, 'R', 'K2'),      # into the hole
    ('K2', 0): (0, 'R', 'K2'),      # skip blanks
    ('K2', 1): (1, 'R', 'K3'),      # destination found
    ('K3', 1): (1, 'R', 'K3'),      # walk the destination
    ('K3', 0): (1, 'R', 'K4'),      # append the first mark
    ('K4', 0): (1, 'L', 'K5'),      # append the second
    ('K5', 1): (1, 'L', 'K5'),      # back over the destination
    ('K5', 0): (0, 'L', 'K6'),
    ('K6', 0): (0, 'L', 'K6'),      # back over the blanks
    ('K6', 1): (0, 'L', 'K7'),      # erase a source mark
    ('K7', 1): (1, 'R', 'K2'),      # more source: append again
    # ('K7', 0) is undefined: halt, the source is exhausted
}


def machine():
    """The repo's simulator keys on integer states; map K1..K7 to 0..6."""
    names = {f'K{i}': i - 1 for i in range(1, 8)}
    t = {}
    for (s, b), (w, d, nxt) in TABLE.items():
        t[(names[s], b)] = (w, d, None if nxt is None else names[nxt])
    return tm.TM(max(names.values()) + 1, t)


def tape_of(source, seeded=1):
    """1^source 0 1^seeded, head at the source's rightmost mark."""
    tape = {i: 1 for i in range(source)}
    tape[source] = 0
    for i in range(seeded):
        tape[source + 1 + i] = 1
    return tape, source - 1, 0


def check(x_max=6):
    m = machine()
    ok = True
    for x in range(1, x_max + 1):
        tape, head, state = tape_of(x)
        steps, tape2, head2, st2, halted = m.run(head=head, state=state,
                                                 tape=tape, max_steps=20000)
        ones = sorted(i for i, v in tape2.items() if v == 1)
        want = list(range(x + 1, x + 1 + 1 + 2 * x))
        good = halted and ones == want
        ok = ok and good
        print(f'  x={x}: steps={steps} halted={halted} marks={ones} '
              f'want={want} {"PASS" if good else "FAIL"}')
    return ok


if __name__ == '__main__':
    print('module K: 1^x 0 1  ->  1^(2x+1) with the source consumed')
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
