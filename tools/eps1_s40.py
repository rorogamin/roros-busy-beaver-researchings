"""eps1's fs-limit question, answered by row experiment: the drain re-cut.

`EPS1_67_PLAN.md` §2 asked whether the fs-limit's 27 states (pass 1: extend
the atom run and shift the index right by two; pass 2: grow the park one mark
per index mark) could be re-cut on the canonical layout.  The cheapest idea
was the drain: a per-slot loop that funds one park mark per index mark with
erase/restore hole trips, skipping the pass-1 shift for the retag's own 2
cells.  This module implements that loop as a standalone device on the same
tape (same frame, same decode) and measures it.

The design facts that shape the rows (all checked by the sweep below):

  * two blank runs sit between every pair of neighbours: the park's gap (with
    the park's anchored right end at C0-3), the chain, the E-to-X gap (the
    chain's top at E, the index at X = E+3).  Inside the chain runs are
    separated by exactly ONE blank, so "two consecutive blanks" is the
    boundary test and both direction walks need a through-and-resume row
    pair to cross one-blank inner gaps.

  * the park grows at the first blank reached walking left from the chain
    (its extension cell, whatever its own right end); the write happens on
    that cell, so p==0 needs no arm: the anchored right end C0-3 is itself
    the extension cell of an empty park.

  * per slot the loop is: erase it, walk left (restored slots, 2 gap cells,
    chain, park), write one mark, walk back right (park, 2 gap cells,
    chain, restored slots), then the hole-surround test: the blank whose
    right neighbour is a mark is the hole (restore it and continue); the
    blank whose right neighbour is blank is past the last slot (restore and
    walk home).  The erases are the index's slots leftmost-first, so the
    restored prefix always sits left of the current hole.

Result: the drain as written needs 20 active states and one halt state, and
halts with the head on E, decode-exactly (p, chain, n) -> (p + n, chain, n),
over fixed-edge and random starts.  The pass-2 of record needs 14.  The
re-cut is worse, and the difference is the walk floor: three field crossings
per direction, each with a through-and-resume pair, plus the hole-surround
test that the 14-pass avoids by a different erase order.  Conclusion for the
40-state target, as written in EPS1_67_PLAN.md §9: the fs-limit's cost is
~27 states on this data layout, re-cutting does not reach below it, and the
total budget stays at the ~120-130 floor; 40 would need a device without a
third growing field (the index has no free sea between park and chain),
which means a different representation of the descent, not a re-cut of
this one.

Run: python tools/eps1_s40.py    (expect ALL OK)
"""

import sys
import random

sys.path.insert(0, 'tools')

import eps1_table as T
from eps1_table import frame as tf_frame, decode as tf_decode
from eps1_chain import NUM, ATOM, ATOM1


class Dev:
    """A fragment machine over named states; halts when a row is missing."""

    def __init__(self):
        self.i = {}
        self.rows = {}

    def S(self, nm):
        if nm not in self.i:
            self.i[nm] = len(self.i)
        return self.i[nm]

    def row(self, nm, sym, w, d, nxt):
        k = (self.S(nm), sym)
        assert k not in self.rows, f'duplicate {nm} {sym}'
        self.rows[k] = (w, d, self.S(nxt) if nxt is not None else None)

    def run(self, tape, head, state, limit=400000):
        steps = 0
        rows = self.rows
        while steps < limit:
            k = (state, tape.get(head, 0))
            if k not in rows:
                return steps, head, state
            w, d, nxt = rows[k]
            tape[head] = w
            if d == 'R':
                head += 1
            elif d == 'L':
                head -= 1
            state = nxt
            steps += 1
        raise TimeoutError('no halt in %d steps' % limit)


def build_drain():
    """(p, chain, n) -> (p + n, chain, n) on the frame's own layout.

    Enter on the home E (the chain's top run's last mark); halt with the
    head on E after the park gained n.  The index's slots are erased
    leftmost-first and restored exactly, so decode-after == decode-before
    with p grown by n.
    """
    d = Dev()
    d.row('W1', 1, 1, 'R', 'W2')     # E: step right onto the gap
    d.row('W2', 0, 0, 'R', 'W2b')    # E+1: through the first gap cell
    d.row('W2b', 0, 0, 'R', 'W3')    # E+2: onto X, the index's first slot
    d.row('W3', 1, 0, 'L', 'W4')     # erase the current slot; step left
    d.row('W3', 0, 0, 'L', 'D0')     # stepped past the last slot: walk home
    d.row('W4', 1, 1, 'L', 'W4')     # over the restored slots leftward
    d.row('W4', 0, 0, 'L', 'W5')     # through the index gap's outer cell E+2
    d.row('W5', 0, 0, 'L', 'W6')     # through E+1; the walk reaches the chain
    d.row('W6', 1, 1, 'L', 'W6')     # over the chain runs leftward
    d.row('W6', 0, 0, 'L', 'W6b')    # through the first blank
    d.row('W6b', 1, 1, 'L', 'W6')    # peek left: a mark: an inner gap, resume
    d.row('W6b', 0, 0, 'L', 'W7')    # second blank: the park gap crossed
    d.row('W7', 1, 1, 'L', 'W7')     # over the park leftward (right end may absent)
    d.row('W7', 0, 1, 'R', 'W10')    # first blank walking left: THE WRITE
    d.row('W10', 1, 1, 'R', 'W10')   # from the new mark: back over the park
    d.row('W10', 0, 0, 'R', 'W11')   # through the park gap's outer cell C0-2
    d.row('W11', 0, 0, 'R', 'W12')   # through C0-1; onto the chain
    d.row('W12', 1, 1, 'R', 'W13')   # onto C0 (a mark); step into the chain walk
    d.row('W13', 1, 1, 'R', 'W13')   # over the chain runs rightward
    d.row('W13', 0, 0, 'R', 'W14')   # through the first blank
    d.row('W14', 1, 1, 'R', 'W13')   # peek right: a mark: an inner gap, resume
    d.row('W14', 0, 0, 'R', 'W15')   # second blank: the index gap crossed
    d.row('W15', 1, 1, 'R', 'W15')   # over the restored slots rightward
    d.row('W15', 0, 0, 'R', 'W16')   # a blank: the hole, or past the last slot
    d.row('W16', 1, 1, 'L', 'W17')   # mark right of the blank: the hole; go back
    d.row('W16', 0, 0, 'L', 'W17')   # blank right of the blank: exhausted
    d.row('W17', 0, 1, 'R', 'W3')    # restore the hole; advance right; loop
    d.row('D0', 1, 1, 'L', 'D1')     # onto the index's rightmost restored slot
    d.row('D1', 1, 1, 'L', 'D1')     # over the index leftward
    d.row('D1', 0, 0, 'L', 'D2')     # through E+2
    d.row('D2', 0, 0, 'L', 'D3')     # onto E: the halt state has no rows
    return d


CASES = [
    (0, [ATOM], 1),
    (0, [ATOM], 2),
    (0, [ATOM, NUM(2)], 1),
    (1, [NUM(3)], 2),
    (2, [ATOM1, NUM(2), NUM(3)], 1),
    (0, [NUM(3), NUM(7)], 2),
    (2, [ATOM, NUM(5), NUM(3)], 2),
    (1, [NUM(1), NUM(2), NUM(3)], 1),
    (0, [ATOM, NUM(2)], 2),
    (3, [ATOM1], 1),
    (0, [NUM(9)], 2),
    (2, [ATOM, NUM(2), NUM(3), NUM(4)], 2),
    (1, [ATOM, NUM(2), NUM(3), NUM(4)], 2),
]


def check_drain():
    print('the drain: (p, chain, n) -> (p+n, chain, n), decode-exact')
    d = build_drain()
    print(f'  device: {len(d.i)} states ({len(d.i) - 1} active + halt), '
          f'{len(d.rows)} rows')
    bad = 0
    ok = trials = 0
    for p, chain, n in CASES:
        trials += 1
        tape, E, home = tf_frame(p, list(chain), n)
        work = dict(tape)
        try:
            steps, head, state = d.run(work, E, d.S('W1'))
        except TimeoutError as exc:
            bad += 1
            print(f'  TIMEOUT p={p} chain={chain} n={n}: {exc}')
            continue
        try:
            got = tf_decode(work, head)
        except Exception as exc:                             # noqa: BLE001
            bad += 1
            print(f'  DECODE FAILED p={p} chain={chain} n={n}: {exc}')
            continue
        pp, ch, nn = got
        if (pp, ch, nn) != (p + n, list(chain), n):
            bad += 1
            print(f'  MISMATCH p={p} chain={chain} n={n}: '
                  f'got ({pp}, {ch}, {nn}) want ({p + n}, {chain}, {n})')
        else:
            ok += 1
    rng = random.Random(5)
    for _ in range(200):
        trials += 1
        p = rng.randint(0, 2)
        n = rng.randint(1, 5)
        chain = [rng.choice([NUM(1), NUM(2), NUM(3), NUM(5), ATOM, ATOM1])] \
            + [rng.choice([NUM(2), NUM(3), ATOM])
               for _ in range(rng.randint(0, 2))]
        tape, E, home = tf_frame(p, list(chain), n)
        work = dict(tape)
        try:
            steps, head, state = d.run(work, E, d.S('W1'))
        except TimeoutError as exc:
            bad += 1
            print(f'  TIMEOUT p={p} chain={list(chain)} n={n}: {exc}')
            continue
        try:
            got = tf_decode(work, head)
        except Exception as exc:                             # noqa: BLE001
            bad += 1
            print(f'  DECODE FAILED p={p} chain={list(chain)} n={n}: {exc}')
            continue
        pp, ch, nn = got
        if (pp, ch, nn) != (p + n, list(chain), n):
            bad += 1
            print(f'  MISMATCH p={p} chain={list(chain)} n={n}: '
                  f'got ({pp}, {ch}, {nn}) want ({p + n}, {list(chain)}, {n})')
        else:
            ok += 1
    print(f'  {ok}/{trials} starts ended decode-exactly')
    return bad == 0


def main():
    print("eps_1's fs-limit pieces, measured as a row experiment")
    print()
    ok = check_drain()
    print()
    print('verdict: the drain of the re-cut is 20 active states; the')
    print('pass-2 of record is 14.  The walk-state floor (three field')
    print('crossings per direction plus the hole-surround test), not the')
    print('loop arithmetic, sets the cost; re-cutting does not beat it.')
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
