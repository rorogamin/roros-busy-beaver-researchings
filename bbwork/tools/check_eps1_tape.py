"""Cross-check rocq/Eps1Tape.v's statements against the machine itself.

The Rocq proofs are about [tbl], generated from tools/eps1_machine.py, so the
table certainly matches.  That does not make the *statements* the configurations
the machine really reaches: a proof can be about a tape no run ever sees.  This
script builds the same frame each theorem starts from, runs the same number of
steps in the Python simulator, and compares the result with the configuration the
theorem concludes -- over several values of every gap and length.

    python tools/check_eps1_tape.py

It proves nothing.  It is the check the proofs cannot make.
"""

import sys

sys.path.insert(0, 'tools')
import eps1_machine as m

W = 40                      # where the wall sits; only gaps and lengths matter


def to_tape(clft, ccur, crgt, w):
    """Zipper with the head at cell [w], nearest-first lists -> tape dict."""
    tape = {w: ccur}
    for i, x in enumerate(clft):
        tape[w - 1 - i] = x
    for i, x in enumerate(crgt):
        tape[w + 1 + i] = x
    return tape


def to_conf(tape, head):
    """Tape dict + head -> (cells left, cell under, cells right), nearest first."""
    lo, hi = min(tape), max(tape)
    clft = [tape.get(i, 0) for i in range(head - 1, lo - 1, -1)]
    crgt = [tape.get(i, 0) for i in range(head + 1, hi + 1)]
    return clft, tape.get(head, 0), crgt


def rep(x, n):
    return [x] * n


def show(l):
    return '[' + ''.join(str(x) for x in l) + ']'


def run(tape, steps):
    t = m.machine()
    return t.run(head=W, state=m.ENTRY, tape=tape, max_steps=steps)


def fixture(clft, ccur, crgt):
    return to_tape(clft, ccur, crgt, W)


def rung_copy(gap, a, b, v):
    """rung_reaches_copy: 2*gap + 7 steps, ENTRY -> WALK one cell right."""
    tape = fixture(rep(0, 1 + gap) + rep(1, 2 + a) + rep(0, b), 1,
                   rep(0, 2) + rep(1, v) + [0, 1])
    steps, t2, head, st, halted = run(tape, 2 * gap + 7)
    clft, ccur, crgt = to_conf(t2, head)
    want_clft = rep(1, 2 + a) + rep(0, gap + 2) + rep(1, 1) + rep(0, b)
    want_clft = rep(1, 1) + rep(0, gap + 2) + rep(1, 1 + a) + rep(0, b)
    want_crgt = rep(0, 1) + rep(1, v) + [0, 1]
    ok = (steps == 2 * gap + 7 and not halted and st == m.WALK
          and head == W + 1 and clft == want_clft and ccur == 0
          and crgt == want_crgt)
    print(f'  copy  gap={gap} a={a} b={b} v={v}: {steps} steps, state={st}, '
          f'head-wall={head - W} {"OK" if ok else "MISMATCH"}')
    if not ok:
        print(f'        want {2 * gap + 7} steps, state={m.WALK}, head-wall=1')
        print(f'        left  got {show(clft)}')
        print(f'        left want {show(want_clft)}')
        print(f'        right got {show(crgt)} want {show(want_crgt)} ccur={ccur}')
    return ok


def rung_halt(gap, b, v):
    """rung_halts: one budget mark, gap + 3 steps to G2, then a halt."""
    tape = fixture(rep(0, 1 + gap) + rep(1, 1) + rep(0, b), 1,
                   rep(0, 2) + rep(1, v) + [0, 1])
    steps, t2, head, st, halted = run(dict(tape), gap + 3)
    clft, ccur, crgt = to_conf(t2, head)
    want_clft = rep(0, b - 1) if b else []
    want_crgt = [0] + rep(0, gap + 1) + [1] + rep(0, 2) + rep(1, v) + [0, 1]
    ok = (steps == gap + 3 and not halted and st == m.G2
          and head == W - gap - 3 and ccur == 0
          and clft == want_clft and crgt == want_crgt)
    s2, t3, h3, st3, halted3 = run(dict(tape), gap + 4)
    ok_halt = (s2 == gap + 4 and halted3 and t3 == t2 and h3 == head)
    print(f'  halt  gap={gap} b={b} v={v}: stop after {steps} steps, '
          f'state={st}, halts next={halted3} '
          f'{"OK" if ok and ok_halt else "MISMATCH"}')
    if not (ok and ok_halt):
        print(f'        want {gap + 3} steps, G2, head-wall={-gap - 3}, ccur=0')
        print(f'        got head-wall={head - W} left {show(clft)} want {show(want_clft)}')
        print(f'        right got {show(crgt)}')
        print(f'        right want {show(want_crgt)}')
        print(f'        halting run: steps {s2} (want {gap + 4}) halted={halted3}')
    return ok and ok_halt


def block_spent(M, a, b, v, st0=None):
    """block_spent_reaches_copy: 2*M + 10 steps, S2 -> WALK, gap one wider."""
    st0 = m.S2 if st0 is None else st0
    tape = fixture(rep(0, 1 + M) + rep(1, 2 + a) + rep(0, b), 0,
                   [1] + rep(0, 2) + rep(1, v) + [0, 1])
    t = m.machine()
    steps, t2, head, st, halted = t.run(head=W, state=st0, tape=dict(tape),
                                        max_steps=2 * M + 10)
    clft, ccur, crgt = to_conf(t2, head)
    want_clft = [1] + rep(0, M + 3) + rep(1, 1 + a) + rep(0, b)
    want_crgt = rep(0, 1) + rep(1, v) + [0, 1]
    ok = (steps == 2 * M + 10 and not halted and st == m.WALK
          and head == W + 2 and clft == want_clft and ccur == 0
          and crgt == want_crgt)
    print(f'  spent M={M} a={a} b={b} v={v} from {st0}: {steps} steps, state={st} '
          f'{"OK" if ok else "MISMATCH"}')
    if not ok:
        print(f'        want {2 * M + 10} steps, WALK, head-wall=2, left {show(want_clft)}')
        print(f'        got  head-wall={head - W} left {show(clft)} cur {ccur} right {show(crgt)}')
    return ok


def main():
    print(f'eps_1 tape statements vs the machine, wall at {W}')
    ok = True
    for gap in (0, 1, 3, 4):
        for a in (0, 1, 5):
            ok &= rung_copy(gap, a, 0, 3)
    for b in (0, 2):
        ok &= rung_copy(3, 1, b, 4)
    for v in (0, 1, 2, 7):
        ok &= rung_copy(3, 1, 0, v)
    for gap in (0, 1, 3):
        for b in (0, 3):
            for v in (0, 1, 4):
                ok &= rung_halt(gap, b, v)
    for M in (0, 1, 5):
        for a in (0, 2):
            ok &= block_spent(M, a, 0, 3, m.S2)
            ok &= block_spent(M, a, 0, 3, m.S1)
    for b in (0, 2):
        ok &= block_spent(2, 1, b, 4, m.S2)
    for v in (0, 1, 6):
        ok &= block_spent(1, 0, 0, v, m.S2)
    print('ALL OK' if ok else 'MISMATCHES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
