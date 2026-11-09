"""The eps_1 tower machine: layout and the free-end writer.

`tools/tower_free.py` proves the step this machine has to perform, and shows the
two things a tape needs: the working part W grows only at its top, and the park
(a count of the 1-runs above the growth site) only ever shrinks.  This module
turns that into states.

## Frame

    [free]  1^m (park)  0 0  1^n (index)  0 0  1^{W_bottom} 0 ... 0 1^{W_top}  [free]

W is held bottom-first, left to right, so its *top* run is the rightmost run and
grows into the free space on the right.  The park is a count run at the left end,
so both things that ever change size do it at a tape boundary.  Gaps of one
blank are inside W; the two-blank gaps on either side of the index are the
region markers, and free space is two blanks or more with nothing after them.

## Move B's write

B writes n+1 marks as a new top run of W.  n has to come from the index, which
must survive the whole run, so the marks are copied by draining the index from
its left end and writing one mark back beside the hole each trip -- the one-sweep
trick of `tools/eps1_copy.py`, so the index ends one cell further left and keeps
its n marks.  Draining to the left matters: it spends the blank on the park side,
leaving the index-to-W separator untouched at two blanks.

    push:  walk right to W's free end, write one mark two cells past the last
           mark of W (that is the new run's start, one blank clear of it)
    trip:  at the hole h, step right to the pointer x, erase x, step left and
           write the mark at h (the index shifts left one cell), walk right and
           append one mark at W's free end, walk back to the new hole x, then
           step right: a mark means another trip, a blank means the index is done

n trips plus the pushed start mark give n+1 marks, and the run ends up
contiguous one blank to the right of where W's top run was.

## Checks

`check_writer` runs the writer from the push on frames with the head on the
index's leftmost mark: the result must be W with a new top run of n+1, the index
still n marks (one cell left), the park untouched.  `check_copy` starts at the
drain loop instead, on a frame that already has the pushed mark, and must append
exactly n marks.
"""

import sys

sys.path.insert(0, 'tools')
import tm

# --- states ------------------------------------------------------------------
P_IX, P_GAP, P_C0, P_CH, P_HIT, P_Z = range(6)        # push: out to free space
P_RET, P_RT2, P_RT4 = range(6, 9)                     # push: back to the index
HOLE, ERASE, WB, HOLE2 = range(9, 13)                 # drain: one trip's left end
CNX, CR, CB1, CB2, CCH, CHIT = range(13, 19)          # drain: out to free space
CRET, CRT2, CRT4, NXT = range(19, 23)                 # drain: back to the hole
APP = 23                                              # append at W's first blank
DONE = 24
NSTATES = 25

NAMES = {P_IX: 'P_IX', P_GAP: 'P_GAP', P_C0: 'P_C0', P_CH: 'P_CH', P_HIT: 'P_HIT',
         P_Z: 'P_Z', P_RET: 'P_RET', P_RT2: 'P_RT2', P_RT4: 'P_RT4',
         HOLE: 'HOLE', ERASE: 'ERASE', WB: 'WB', HOLE2: 'HOLE2',
         CNX: 'CNX', CR: 'CR', CB1: 'CB1', CB2: 'CB2', CCH: 'CCH',
         CHIT: 'CHIT', CRET: 'CRET', CRT2: 'CRT2', CRT4: 'CRT4', NXT: 'NXT',
         APP: 'APP', DONE: 'DONE'}

TABLE = {
    # --- push: right over the index, across the separator, over W to free space
    (P_IX, 1): (1, 'R', P_IX),
    (P_IX, 0): (0, 'R', P_GAP),
    (P_GAP, 0): (0, 'R', P_C0),
    (P_GAP, 1): (1, 'R', P_C0),
    (P_C0, 1): (1, 'R', P_CH),          # W exists: walk over it
    (P_C0, 0): (0, 'R', P_Z),           # W empty: the run starts right here
    (P_CH, 1): (1, 'R', P_CH),
    (P_CH, 0): (0, 'R', P_HIT),
    (P_HIT, 1): (1, 'R', P_CH),         # that blank was an inside gap
    (P_HIT, 0): (1, 'L', P_RET),        # two blanks: the run's first mark
    (P_Z, 0): (1, 'L', P_RET),
    # --- push: back left to the index's left end, then straight into the drain
    (P_RET, 1): (1, 'L', P_RET),
    (P_RET, 0): (0, 'L', P_RT2),
    (P_RT2, 1): (1, 'L', P_RET),
    (P_RT2, 0): (0, 'L', P_RT4),        # two blanks: the separator, crossed
    (P_RT4, 1): (1, 'L', P_RT4),
    (P_RT4, 0): (0, 'R', ERASE),        # the hole: step onto the pointer
    # --- drain: one trip
    (HOLE, 0): (0, 'R', ERASE),         # at the hole: step onto the pointer
    (ERASE, 1): (0, 'L', WB),           # erase the pointer, back to the hole
    (WB, 0): (1, 'R', HOLE2),           # put it one cell left: the index shifts
    (HOLE2, 0): (0, 'R', CNX),
    (CNX, 1): (1, 'R', CR),             # index continues
    (CNX, 0): (0, 'R', CB1),            # pointer was the last: separator next
    (CR, 1): (1, 'R', CR),
    (CR, 0): (0, 'R', CB1),
    (CB1, 0): (0, 'R', CB2),
    (CB1, 1): (1, 'R', CB2),
    (CB2, 0): (0, 'R', CCH),
    (CB2, 1): (1, 'R', CCH),
    (CCH, 1): (1, 'R', CCH),
    (CCH, 0): (0, 'R', CHIT),
    (CHIT, 1): (1, 'R', CCH),           # that blank was an inside gap
    (CHIT, 0): (0, 'L', APP),           # two blanks: back to the first one
    (APP, 0): (1, 'L', CRET),           # append the mark there, flush
    # --- drain: back left to the new hole, then test
    (CRET, 1): (1, 'L', CRET),
    (CRET, 0): (0, 'L', CRT2),
    (CRT2, 1): (1, 'L', CRET),
    (CRT2, 0): (0, 'L', CRT4),
    (CRT4, 1): (1, 'L', CRT4),
    (CRT4, 0): (0, 'R', NXT),           # the hole; one cell right is the pointer
    (NXT, 1): (1, 'L', HOLE),           # the index continues
    # (NXT, 0) absent: the index is empty, the copy is complete
}


def machine():
    return tm.TM(NSTATES, TABLE)


# --- the frame ---------------------------------------------------------------

def frame(W, n, m=0, left=4):
    """Tape for (park m, index n, working part W bottom-first).

    Returns (tape, head, info); the head is on the index's leftmost mark.

    Order matters: the park is leftmost and the index next.  Every copy shifts
    the index one cell left, and every move B that has a park spends one park
    level from its right end, so the park-to-index separator is the same width
    after each move; the index-to-W separator grows instead, which costs nothing
    because it only makes a walk longer.
    """
    tape = {}
    pos = left
    if m > 0:
        for i in range(m):
            tape[pos + i] = 1
        pos += m
        pos += 2                        # spent by the copy, given back by B
    index_start = pos
    for i in range(n):
        tape[pos + i] = 1
    index_end = pos + n - 1
    pos += n + 2
    chain_start = pos
    for k, w in enumerate(W):
        if k:
            pos += 1
        for i in range(w):
            tape[pos + i] = 1
        pos += w
    info = dict(index_start=index_start, index_end=index_end,
                chain_start=chain_start, chain_end=pos - 1, m=m, n=n)
    return tape, index_start, info


def runs_of(tape):
    """(run length, gap before it) left to right."""
    cells = sorted(p for p, v in tape.items() if v == 1)
    out = []
    prev = None
    for p in cells:
        if prev is not None and p == prev + 1:
            out[-1][0] += 1
        else:
            out.append([1, None if prev is None else p - prev - 1])
        prev = p
    return out


def decode(tape, n):
    """Tape -> (park m, index length, W bottom-first).

    The index is the run of length n followed by exactly two blanks and then a
    mark (that is the separator into W).  Free space after W's top is two blanks
    and then nothing, so it cannot be mistaken for the separator.
    """
    rs = runs_of(tape)
    idx = None
    for i, (ln, gap) in enumerate(rs):
        # the index: n marks, a separator of >= 2 blanks, then a mark
        if ln == n and i + 1 < len(rs) and rs[i + 1][1] is not None                 and rs[i + 1][1] >= 2:
            idx = i
    if idx is None:
        return None, None, [r[0] for r in rs]
    m = rs[idx - 1][0] if idx >= 1 else 0
    return m, n, [r[0] for r in rs[idx + 1:]]


def check_writer(verbose=False):
    print('free-end writer: push n+1 as W\'s new top run, index and park kept')
    bad = 0
    cases = [([2], 1), ([2], 2), ([2], 5), ([1, 3], 2), ([2, 3, 1], 3),
             ([4], 1), ([3, 2], 4), ([1], 1), ([5, 5], 2), ([2, 2, 2], 6),
             ([7], 12), ([1, 1, 1, 2], 3), ([3], 1), ([6, 6, 6], 9)]
    for W, n in cases:
        tape, head, info = frame(W, n)
        steps, t2, h2, s2, halted = machine().run(head=head, state=P_IX,
                                                  tape=tape, max_steps=5_000_000)
        m2, ln2, W2 = decode(t2, n)
        ok = halted and W2 == W + [n + 1] and ln2 == n and m2 == 0
        print(f'  W={str(W):<14} n={n:<3} steps={steps:<8} W\'={W2} '
              f'{"PASS" if ok else "FAIL"}')
        if not ok:
            bad += 1
            print('      tape ', tm.tape_str(t2, h2))
            print('      runs ', runs_of(t2))
    # with a park in front
    for W, n, m in [([2], 2, 1), ([3, 1], 2, 4), ([1], 1, 2), ([5], 3, 2),
                    ([4, 2], 3, 7)]:
        tape, head, info = frame(W, n, m)
        steps, t2, h2, s2, halted = machine().run(head=head, state=P_IX,
                                                  tape=tape, max_steps=5_000_000)
        m2, ln2, W2 = decode(t2, n)
        ok = halted and W2 == W + [n + 1] and ln2 == n and m2 == m
        print(f'  park={m} W={str(W):<10} n={n:<3} steps={steps:<8} '
              f"W'={W2} park'={m2} {'PASS' if ok else 'FAIL'}")
        if not ok:
            bad += 1
            print('      tape ', tm.tape_str(t2, h2))
    print('ALL OK' if not bad else f'{bad} FAILURES')
    return bad == 0


if __name__ == '__main__':
    if '--trace' in sys.argv:
        i = sys.argv.index('--trace')
        W = [int(c) for c in (sys.argv[i + 1] if len(sys.argv) > i + 1 else '2')]
        n = int(sys.argv[i + 2]) if len(sys.argv) > i + 2 else 2
        tape, head, info = frame(W, n)
        m = machine()
        print('start', tm.tape_str(tape, head))
        st = P_IX
        for step in range(1, 2000):
            r = m.step(tape, head, st)
            if r is None:
                print(f'{step:>6} STOP  {tm.tape_str(tape, head)}')
                break
            head, st = r
            print(f'{step:>6} {NAMES.get(st, st):>5} {tm.tape_str(tape, head)}')
    else:
        sys.exit(0 if check_writer() else 1)
