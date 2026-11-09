"""The nine-state copy primitive of FGH_HANDBOOK §10.2, implemented and tested.

Spec as listed in the handbook (C0..C8, 1 = mark, 0 = blank):

    C0  at the mark:      1 -> 0,R,C1        erase the cell you are carrying
    C1  walk right:       1 -> 1,R,C1 ; 0 -> 0,R,C2
    C2  second separator: 0 -> 0,R,C3
    C3  walk over dest:   1 -> 1,R,C3 ; 0 -> 1,L,C4    write the copy
    C4  walk back:        1 -> 1,L,C4 ; 0 -> 0,L,C5
    C5  separator:        0 -> 0,L,C6
    C6  second separator: 0 -> 0,L,C7
    C7  over source:      1 -> 1,L,C7 ; 0 -> 1,R,C8    restore the mark
    C8  next cell:        1 -> 1,R,C0 ; 0 -> halt      done

Measured behaviour (this file, `python tools/copy.py`):

  * the literal table, with a doubled separator, halts in C6 on the source's
    rightmost mark at step 9 for 1^3: C6 has no transition on 1, and the walk
    back from the destination cannot reach the source's left end through it.
  * giving C6 `1 -> 1,L,C7` (so it may pass a mark) fixes that step, but the
    copy still does not copy: for 1^3 it copies one cell and then drifts, and
    for 1^2 it terminates after 11 steps having produced one mark instead of
    two, halting in C0 on a separator.

The reason is structural, not a table bug: C7 restores the carried mark
(`0 -> 1,R,C8`), so after the first pass the source has no zero left to stop
the *next* pass's walk.  The marker is destroyed by its own restoration, and
each pass then walks one cell further left than the pass before, which is the
drift the simulation shows.  With two symbols there is no second marker to
keep an anchor, so a copy has to grow into blank tape on one side instead of
rewriting a block in place -- which is exactly what the engine in
`tools/stack.py` does (it copies leftward into untouched tape, `c -> 2c + 2`).

Consequence for the §10.3 blueprint: the refill and the push both need this
primitive, so the exact growing-stack machine cannot be assembled from the
handbook's nine states as listed.  It needs either a wider alphabet (a real
marker symbol) or a copy that never restores its marker.
"""
import tm

HALT = None

# literal §10.2 listing, C0..C8 at states 0..8
COPY_LITERAL = {
    (0, 1): (0, 'R', 1),
    (1, 1): (1, 'R', 1), (1, 0): (0, 'R', 2),
    (2, 0): (0, 'R', 3),
    (3, 1): (1, 'R', 3), (3, 0): (1, 'L', 4),
    (4, 1): (1, 'L', 4), (4, 0): (0, 'L', 5),
    (5, 0): (0, 'L', 6),
    (6, 0): (0, 'L', 7),
    (7, 1): (1, 'L', 7), (7, 0): (1, 'R', 8),
    (8, 1): (1, 'R', 0), (8, 0): (0, 'R', HALT),
}


def literal_with_pass():
    """The literal table with C6 allowed to pass a mark on its way left."""
    t = dict(COPY_LITERAL)
    t[(6, 1)] = (1, 'L', 7)
    return t


def run(table, k, gap=2, max_steps=5000, start=0):
    """Copy 1^k (at cells 0..k-1) across `gap` blanks, destination to its right."""
    m = tm.TM(9, table)
    tape = {i: 1 for i in range(k)}
    steps, tp, head, state, halted = m.run(head=start, state=0, tape=tape,
                                           max_steps=max_steps)
    kept = all(tp.get(i, 0) == 1 for i in range(k))
    dest = sorted(i for i in range(k + gap, k + gap + 2 * k + 4) if tp.get(i, 0) == 1)
    return steps, halted, state, head, kept, dest, m.score(tp)


if __name__ == '__main__':
    for k in (1, 2, 3, 4):
        for name, t in (('literal gap=2', COPY_LITERAL),
                        ('literal gap=3', COPY_LITERAL),
                        ('C6-pass gap=2', literal_with_pass())):
            gap = 3 if 'gap=3' in name else 2
            steps, halted, state, head, kept, dest, score = run(t, k, gap=gap)
            print(f'{name} k={k}: steps={steps} halted={halted} state={state} '
                  f'src_intact={kept} dest={dest} score={score} '
                  f'{"OK" if kept and len(dest) == k else "WRONG"}')
