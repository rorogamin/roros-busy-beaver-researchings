"""Dump the fixed eps_0 drive's configurations with blank ends trimmed.

Nearest-first zipper lists (the `rocq/TM.v` convention), written as runs, with
trailing blanks dropped from both sides -- the tape is blank out there, so the
trimmed form is the exact one to state a lemma about.
"""

import sys

sys.path.insert(0, 'tools')
import tm
from eps0_machine import TABLE, NAMES
from eps0_machine import R0, R1, R2, R4, R5, R6, A5, A6, A7, A8, A9, AA
from eps0_machine import F0, F1, F2, F3, F4, F5, P0, P1, P2
from eps0_machine import S0, S1, S2, S3, S4, K1, K2, K3, K4, K5, K6, K7


def rle(xs):
    if not xs:
        return '-'
    out, run, prev = [], 0, None
    for x in xs:
        if x == prev:
            run += 1
        else:
            if prev is not None:
                out.append(f'{prev}^{run}')
            prev, run = x, 1
    out.append(f'{prev}^{run}')
    return ' '.join(out)


def trim_left(left):
    """Drop blanks past the last mark (blanks further left are blank tape)."""
    i = len(left)
    while i and left[i - 1] == 0:
        i -= 1
    return left[:i]


def trim_right(right):
    i = 0
    for j, v in enumerate(right):
        if v:
            i = j + 1
    return right[:i]


def tape_conf(tape, head, width=64):
    left = trim_left([tape.get(head - 1 - i, 0) for i in range(width)])
    right = trim_right([tape.get(head + 1 + i, 0) for i in range(width)])
    return left, tape.get(head, 0), right


def start(n, v):
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


def walk(n, v, states, limit=3000000, maxhits=40):
    m = tm.TM(33, TABLE)
    tape, head, st = start(n, v)
    hits = 0
    step = 0
    prev = None
    while step < limit and hits < maxhits:
        if st in states and st != prev:
            left, cur, right = tape_conf(tape, head)
            print(f'  {step:>7} {NAMES[st]:>3} L[{rle(left)}] <{cur}> R[{rle(right)}]')
            hits += 1
        r = m.step(tape, head, st)
        if r is None:
            print(f'  {step + 1:>7} HALT')
            return
        step += 1
        prev = st
        head, st = r


if __name__ == '__main__':
    if '--costs' in sys.argv:
        for n, v in ((1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 5)):
            m = tm.TM(33, TABLE)
            tape, head, st = start(n, v)
            steps, t2, h2, s2, halted = m.run(head=head, state=st, tape=tape,
                                              max_steps=30000000)
            total = sum(1 for x in t2.values() if x == 1)
            print(f'n={n} v={v}: steps={steps} halted={halted} marks={total}')
    else:
        n, v = (int(x) for x in (sys.argv[1:3] or ['1', '1']))
        names = sys.argv[3:] if len(sys.argv) > 3 else ['F0', 'R1', 'K2', 'A5']
        sel = {globals()[x] for x in names}
        walk(n, v, sel)
