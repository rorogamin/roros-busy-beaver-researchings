"""The eps_1 machine from a blank tape: the prologue that writes its own frame.

`eps1_machine` is proved (and checked) from the frame

    1^{a+1}(budget) 0^1 [block: empty] 1(wall) 0^2 1^v 0 1(seed)

with the head on the wall in `ENTRY`.  A bbchallenge entry has to start from
nothing: state 0, every cell blank, head at 0.  This module adds the prologue
that lays that frame down and then hands over to `ENTRY` on the wall.

The prologue writes the frame **right to left**, starting at cell 0 with the
seed, so the wall is not written until the end: walking left it puts down seed,
the blank, the value, the value gap, the wall, the block region and the budget,
and finishes at the budget's far end.  One return pass -- skip the budget marks,
skip the block region, stop at the wall -- lands on the wall in `ENTRY`, exactly
the frame `eps1_machine.start` builds by hand.

Nothing here is a proof; the runs are checked against the ladder `lvl` that
`rocq/Eps1Ladder.v` specifies.
"""

import sys

sys.path.insert(0, 'tools')
import tm
import eps1_machine as m1

BLOCK_GAP = 1          # blanks between the budget and the wall (block region)
VAL_GAP = 2            # blanks between the wall and the value

HANDOVER = -1          # prologue target meaning "the machine's ENTRY"
HANDOVER_G1 = -2       # ... and "G1", the step ENTRY takes off the wall


def prologue(a, v, block_gap=BLOCK_GAP, val_gap=VAL_GAP):
    """Rows of the prologue, its state count, and where the wall ends up.

    Cells, in the order the head meets them walking left from cell 0:
    seed, blank, the value, the value gap, the wall, the block region, budget.
    """
    cells = ([1] + [0] + [1] * v + [0] * val_gap + [1]
             + [0] * block_gap + [1] * (a + 1))
    n = len(cells)                          # writing states 0 .. n-1
    skip_marks, skip_blanks = n, n + 1
    nstates = n + 2
    wall = -(2 + v + val_gap)
    assert cells[-wall] == 1                # the wall is where the return stops
    rows = {}

    def put(s, sym, w, d, t):
        rows[(s, sym)] = (w, d, t)

    for i, c in enumerate(cells):
        last = (i == n - 1)
        for sym in (0, 1):                  # the tape is blank; rows defined anyway
            put(i, sym, c, 'R' if last else 'L',
                skip_marks if last else i + 1)
    put(skip_marks, 1, 1, 'R', skip_marks)
    put(skip_marks, 0, 0, 'R', skip_blanks)
    put(skip_blanks, 0, 0, 'R', skip_blanks)
    # the wall: the head is on it, and ENTRY's own first step is (1, L, G1), so
    # the return spends that step here instead of landing in ENTRY to spend it
    put(skip_blanks, 1, 1, 'L', HANDOVER_G1)
    return rows, nstates, wall


def machine(a, v, block_gap=BLOCK_GAP, val_gap=VAL_GAP):
    """The blank-tape machine: prologue states first, so the start state is 0."""
    prows, pn, wall = prologue(a, v, block_gap, val_gap)
    rows = {}
    for (s, r), (w, d, t) in prows.items():
        rows[(s, r)] = (w, d, {HANDOVER: m1.ENTRY, HANDOVER_G1: m1.G1}[t] + pn
                        if t in (HANDOVER, HANDOVER_G1) else t)
    for (s, r), (w, d, t) in m1.TABLE.items():
        rows[(s + pn, r)] = (w, d, t + pn)
    return tm.TM(pn + m1.NSTATES, rows), pn + m1.NSTATES, rows, wall


def refine(nstates, rows):
    """Partition refinement: how many states the table really needs."""
    def key0(s):
        return tuple(None if (s, r) not in rows else rows[(s, r)][:2] for r in (0, 1))
    idx, part = {}, [0] * nstates
    for s in range(nstates):
        part[s] = idx.setdefault(key0(s), len(idx))
    while True:
        idx, new = {}, [0] * nstates
        for s in range(nstates):
            sig = tuple(None if (s, r) not in rows
                        else (rows[(s, r)][0], rows[(s, r)][1], part[rows[(s, r)][2]])
                        for r in (0, 1))
            new[s] = idx.setdefault(sig, len(idx))
        if new == part:
            return part, len(idx)
        part = new


def run(a, v, block_gap=BLOCK_GAP, val_gap=VAL_GAP, max_steps=2_000_000):
    m, nstates, rows, wall = machine(a, v, block_gap, val_gap)
    steps, tape, head, st, halted = m.run(head=0, state=0, tape={},
                                          max_steps=max_steps)
    return dict(a=a, v=v, nstates=nstates, nrows=len(rows), steps=steps,
                value=m1.value(tape, wall), want=m1.lvl(a, v), halted=halted,
                state=st, tape=tape, head=head, wall=wall,
                merged=refine(nstates, rows)[1],
                used=len({s for s, _ in rows}))


def table(a, v):
    """The machine as five-tuples, states contiguous from 0, blank = 0."""
    m, nstates, rows, wall = machine(a, v)
    out = []
    for s in range(nstates):
        for r in (0, 1):
            if (s, r) in rows:
                w, d, t = rows[(s, r)]
                out.append(f'{s} {r} {w} {d} {t}')
            else:
                out.append(f'{s} {r} - - -')       # halts here
    return '\n'.join(out)


def check():
    print('eps_1 from a blank tape: state 0, empty tape, head at 0')
    ok = True
    for a, v in ((0, 1), (0, 2), (0, 5), (1, 1), (1, 2)):
        r = run(a, v)
        good = r['halted'] and r['value'] == r['want']
        ok = ok and good
        print(f"  a={a} v={v}: {r['used']} states ({r['merged']} after merge), "
              f"{r['nrows']} rows, steps={r['steps']}, value={r['value']} "
              f"want={r['want']} {'PASS' if good else 'FAIL'}")
        if not good:
            t = m1.render(r['tape'], r['head'])
            print(f'      head={r["head"]} tape head-40: {t[max(0,len(t)//2-40):len(t)//2+40]}')
    return ok


if __name__ == '__main__':
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
