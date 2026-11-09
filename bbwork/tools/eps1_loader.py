"""The eps_1 machine as loader + carving + engine: blank tape to an eps_1 claim.

The loader is a 6-state machine that halts with ~10^^15 ones in one run on an
otherwise blank tape:

    A _ 1 r B     B _ 1 r C     C _ 1 l C     D _ _ l E     E _ 1 l F     F _ _ r C
    A 1 _ l D     B 1 _ r F     C 1 1 l A     D 1 1 r halt  E 1 _ r B     F 1 _ r E

Its output is a contiguous run of marks, so the engine's frame has to be *carved*
out of it rather than written: the first marks of the run are the budget, then a
blank (the block region), the wall, a two-blank gap, the rest of the run (the
value), a blank, and the last mark (the seed).

    1^{a+1} 0 1 0 0 1^v 0 1

Carving from the left end costs one state per cell, so the glue is short: two
states to normalise onto the run's left end, six to place budget/block/wall/gap,
one to skip the value to its right end, three to erase the mark before the seed
and come back, and one more to step onto the wall in `ENTRY`.

The full machine cannot be run -- 10^^15 marks is not a tape -- so what is
checked here is the part that can be: the carving, fed a short run `1^N` standing
in for the loader's output, against the ladder `lvl` the engine implements.
"""

import sys

sys.path.insert(0, 'tools')
import tm
import eps1_machine as m1

# --- the loader the user supplied: 6 states, _ = 0 ---------------------------
LOADER = {
    ('A', 0): (1, 'R', 'B'),
    ('A', 1): (0, 'L', 'D'),
    ('B', 0): (1, 'R', 'C'),
    ('B', 1): (0, 'R', 'F'),
    ('C', 0): (1, 'L', 'C'),
    ('C', 1): (1, 'L', 'A'),
    ('D', 0): (0, 'L', 'E'),
    ('D', 1): (1, 'R', None),        # halts
    ('E', 0): (1, 'L', 'F'),
    ('E', 1): (0, 'R', 'B'),
    ('F', 0): (0, 'R', 'C'),
    ('F', 1): (0, 'R', 'E'),
}
LOADER_ORDER = ['A', 'B', 'C', 'D', 'E', 'F']

A, BUDGET = 2, 2   # budget marks in the frame (a = 1: one rung)


def carve(block_gap=1, val_gap=2):
    """Glue states after the loader, in their own numbering.

    Returns the rows, the state count and the handover state.
    """
    rows = {}
    n = 0

    def new():
        nonlocal n
        n += 1
        return n - 1

    # 1. normalise onto the run's left end: walk left while on a mark, then the
    #    cell left of the run is blank, so step right onto the leftmost mark
    walk_l = new()
    rows[(walk_l, 1)] = (1, 'L', walk_l)
    # 2. the frame, left to right, one state per cell: budget, block gap, wall,
    #    value gap; then the value is skipped to its right end
    budget = [new() for _ in range(A)]
    gaps_a = [new() for _ in range(block_gap)]
    wall = new()
    gaps_v = [new() for _ in range(val_gap)]
    skip_r = new()
    chain = ([('keep', s) for s in budget] + [('erase', s) for s in gaps_a]
             + [('keep', wall)] + [('erase', s) for s in gaps_v])
    rows[(walk_l, 0)] = (0, 'R', chain[0][1])
    for i, (what, s) in enumerate(chain):
        rows[(s, 1)] = (1, 'R', chain[i + 1][1] if i + 1 < len(chain) else skip_r)
    rows[(skip_r, 1)] = (1, 'R', skip_r)
    back_1 = new()           # just past the right end -> the seed
    back_2 = new()           # the seed -> the mark to erase
    walk_val = new()         # left over the value
    gap_2 = new()
    rows[(skip_r, 0)] = (0, 'L', back_1)
    rows[(back_1, 1)] = (1, 'L', back_2)
    rows[(back_2, 1)] = (0, 'L', walk_val)   # erase it, step left into the value
    rows[(walk_val, 1)] = (1, 'L', walk_val)
    rows[(walk_val, 0)] = (0, 'L', gap_2)
    rows[(gap_2, 0)] = (0, 'L', m1.ENTRY)      # off the last gap cell onto the wall
    erases = {s for what, s in chain if what == 'erase'}
    for s in erases:
        rows[(s, 1)] = (0, 'R', rows[(s, 1)][2])
    return rows, n, chain[0][1]


def machine(block_gap=1, val_gap=2):
    """Loader, then the carving, then the engine; the loader's A becomes state 0."""
    glue, ng, start = carve(block_gap, val_gap)
    base = len(LOADER_ORDER)          # the engine goes after the loader and glue
    rows = {}
    for (st, sy), (w, d, t) in LOADER.items():
        tgt = None if t is None else LOADER_ORDER.index(t)
        if tgt is None:
            tgt = start + len(LOADER_ORDER)      # the halt hands over to the carving
        rows[(LOADER_ORDER.index(st), sy)] = (w, d, tgt)
    for (s, r), (w, d, t) in glue.items():
        engine = t + len(LOADER_ORDER) + ng if t in (m1.ENTRY, m1.WALK) else None
        rows[(s + len(LOADER_ORDER), r)] = (w, d, engine if engine is not None
                                            else t + len(LOADER_ORDER))
    for (s, r), (w, d, t) in m1.TABLE.items():
        rows[(s + len(LOADER_ORDER) + ng, r)] = (w, d, t + len(LOADER_ORDER) + ng)
    eng = 1 + max(s for s, _ in m1.TABLE)
    return tm.TM(len(LOADER_ORDER) + ng + eng, rows), rows


def run_carved(n, block_gap=1, val_gap=2, max_steps=3_000_000):
    """Carving plus engine, on the run `1^n` standing in for the loader's output."""
    m, rows = machine(block_gap, val_gap)
    off = len(LOADER_ORDER)
    tape = {i: 1 for i in range(n)}
    steps, t2, h2, s2, halted = m.run(head=0, state=off, tape=tape,
                                      max_steps=max_steps)
    # the frame's wall sits at 1 + block_gap after the run's left end
    wall = BUDGET + block_gap
    v = n - (BUDGET + block_gap + 1 + val_gap) - 2     # run minus budget, wall, gaps, seed
    return dict(n=n, steps=steps, halted=halted, wall=wall,
                value=m1.value(t2, wall), want=m1.lvl(1, v), v=v)


def check():
    print('eps_1 as loader + carve + engine: the carving checked on a short run')
    ok = True
    for n in (9, 10):
        r = run_carved(n)
        good = r['halted'] and r['value'] == r['want']
        ok = ok and good
        print(f"  run 1^{n}: v={r['v']} steps={r['steps']} value={r['value']} "
              f"want={r['want']} {'PASS' if good else 'FAIL'}")
    m, rows = machine()
    used = len({s for s, _ in rows})
    print(f'full machine: {used} states, {len(rows)} rows')
    return ok


if __name__ == '__main__':
    ok = check()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
