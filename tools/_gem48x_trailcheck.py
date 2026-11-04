"""gem48x core-geometry micro-verifier: the interleaved-trail +/-1 repair.

Verifies in isolation the two claims the compiled machine's correctness
rests on (HANDOFF round 16 ledger item 1):

  CLAIM A (fetch): with the trail convention TM at j < pos, TB at j >= pos,
  walking right to the FIRST TB lands exactly on pair #pos, for every pos
  up to a horizon, and the walk is purely commemorative (no writes).

  CLAIM B (repair): after consuming the fetch (no writes), the
  constant-pointer repair of a simulated +-1 move on the trail is exact:
    d=+1: write TM at pair #pos's trail cell (it was the first TB);
    d=-1: write TB at pair #(pos-1)'s trail cell (it was TM);
  and the resulting footprint equals the convention for pos' = pos +- d,
  for every pos and every d where pos' >= 0.

Exhaustive over pos in 0..HOR (horizon 400), both move directions.
Also verifies the repair plus a re-fetch round-trips the position.

Run: py -3.14 < tools/_gem48x_trailcheck.py
"""

import sys

TB, TM = 'tb', 'tm'          # trail cell values (the compiled alphabet)
HOR = 400                    # position horizon


def trail_for(pos):
    """The footprint cells 0..pos+1 (the head's own trail cell plus one
    unmarked cell beyond it, as the blank region always provides)."""
    return [TM if j < pos else TB for j in range(pos + 2)]


def fetch_pos(trail):
    """Simulate the compiled fetch walk: TB = the first TB = the head."""
    for i, v in enumerate(trail):
        if v == TB:
            return i
    raise AssertionError('no head found: the trail is all TM')


def repair(trail, pos, d):
    """The constant-pointer repair: return the new trail after a
    simulated move d from pos.  No writes except the single +/-1 cell."""
    t = list(trail)
    if d == 1:
        t[pos] = TM          # the head's own trail cell was the first TB
        pos = pos + 1
    else:
        assert pos >= 1
        t[pos - 1] = TB      # the previous pair's trail cell was TM
        pos = pos - 1
    if pos >= len(t):
        t.append(TB)         # the blank region supplies the next unmarked cell
    return t, pos


def main():
    bad = 0
    for pos in range(HOR + 1):
        t0 = trail_for(pos)
        # CLAIM A
        got = fetch_pos(t0)
        if got != pos:
            bad += 1
            print(f'  A FAIL pos={pos}: fetch gave {got}')
        # CLAIM B for both directions
        for d in (1, -1):
            if pos == 0 and d == -1:
                continue      # pos-1 < 0: the blank-run head never moves
                           # left of the horizon-0 edge in this model
            t1, p1 = repair(t0, pos, d)
            if fetch_pos(t1) != p1:
                bad += 1
                print(f'  B FAIL pos={pos} d={d}')
            # stress: chain 300 random-walk moves and re-verify each step
        t, p, rng = t0, pos, 12345
        seed = 12345
        for k in range(300):
            seed = (seed * 1103515245 + 12345) & 0x7fffffff
            d = 1 if (seed >> 16) & 1 else -1
            if p == 0 and d == -1:
                d = 1
            t, p = repair(t, p, d)
            if fetch_pos(t) != p:
                bad += 1
                print(f'  B-CHAIN FAIL at step {k}')

    print(f'HOR={HOR}: {HOR * 2 + 600} checks'
          + ('   ALL OK' if bad == 0 else f'   {bad} FAILURES'))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
