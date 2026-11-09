"""gem48x fetch-path rehearsal (HANDOFF round 16 ledger item 3, part i).

Rehearses, as an explicit (phase, symbol) -> (write, dir, next) table
run by a generic interpreter, the head-fetch/repair machinery the
compiled machine needs each cycle (NOT yet the full phase table):

  THE FETCH: the head walk from HOME along the interleaved trail
  pairs is purely commemorative (no writes): first TB = the head
  pair's own trail cell; then ONE step right = the head pair's data
  cell, where THE BIT READ HAPPENS = the runner-peek: ONE cell only,
  no w/d/halt*-part rows needed (they stay read-only at HOME).
  b = the bit value at the head pair's data cell (1 = ODD pair).

  THE DOUBLED FRONT (the plan's carried two-phase copy): the move d
  of the PREVIOUS cycle is carried by the fetch front itself (the
  front phases come in a d=0 and a d=1 flavour); only then can the
  DBIT read branch by b into the repair with BOTH carries resolved.

  THE DEFERRED +-1 REPAIR (the trailcheck convention):
    d=+1: write TM at the head pair's own trail cell;
    d=-1: keep TB there; write TB at the PREVIOUS pair's trail cell
      (the first left TM = the new boundary);
  then keep-everything-left to HOME and park.  The park phase must
  be the paired copy carrying (b, d) exactly, the repaired footprint
  must satisfy the trail convention at the new head (pos + d), and
  the sweep checks the whole layout byte-for-byte outside the cell
  the cycle is allowed to touch.

Chaining: repeated cycles from every start pos (200 random d-steps
each, plus the 0/edge starts on every pos), verifying every park,
trail and data bit.

Run: py -3.14 < tools/_gem48x_newfetch.py
"""

import sys

HOME, TB, TM, B0v, B1v = 0, 1, 2, 3, 4
HOR = 400
NB = HOR + 1                                        # pairs 0..400

T = {}

def row(ph, sym, w, d, nx):
    T.setdefault(ph, {}).setdefault(sym, (w, d, nx))

for dd in (0, 1):
    # the fetch front, doubled by the carried previous-move d
    row(f'W0{dd}', HOME, HOME, 1, f'H1{dd}')
    row(f'B0{dd}', HOME, HOME, 1, f'W0{dd}')
    row(f'W0{dd}', TM, TM, 1, f'H1{dd}')            # pos-0 edge
    row(f'W0{dd}', TB, TB, 1, f'DBIT{dd}')          # pos-0 edge
    row(f'H1{dd}', TM, TM, 1, f'H1{dd}')            # commemorative walk
    row(f'H1{dd}', B0v, B0v, 1, f'H1{dd}')          # ...through data cells
    row(f'H1{dd}', B1v, B1v, 1, f'H1{dd}')
    row(f'H1{dd}', TB, TB, 1, f'DBIT{dd}')          # first TB = the head
    row(f'DBIT{dd}', B0v, B0v, -1, f'RP0{dd}')      # the runner-peek read
    row(f'DBIT{dd}', B1v, B1v, -1, f'RP1{dd}')
    for bb in (0, 1):
        rp = f'RP{bb}{dd}'
        if dd == 0:
            row(rp, TB, TM, -1, f'L{bb}{dd}')       # ++ repair
        else:
            row(rp, TB, TB, -1, f'L{bb}{dd}')       # -- keeps its marker
        lq = f'L{bb}{dd}'
        for s in (B0v, B1v):
            row(lq, s, s, -1, lq)
        if dd == 0:
            row(lq, TM, TM, -1, f'K{bb}{dd}')       # ++: no other write
        else:
            row(lq, TM, TB, -1, f'K{bb}{dd}')       # --: new boundary
        kq = f'K{bb}{dd}'
        for s in (TM, B0v, B1v):
            row(kq, s, s, -1, kq)
        row(kq, HOME, HOME, 1, f'PB{bb}{dd}')       # the park record
        row(lq, HOME, HOME, 1, f'PB{bb}{dd}')       # pos-0 edge park

def run_machine(cells, head, phase, max_steps=200_000):
    steps = 0
    ph = phase
    while not ph.startswith('PB'):
        r = T[ph].get(cells[head])
        if r is None:
            raise AssertionError(f'death: {ph} on symbol {cells[head]} at {head}')
        w, d, nx = r
        cells[head] = w
        head += d
        ph = nx
        steps += 1
        if steps > max_steps:
            raise AssertionError('budget')
    return ph, steps                                # park, steps


def bit_at(j):
    return 1 if (j * 7919) % 3 == 0 else 0


def build_layout(bits):
    """Cells 0..2*NB: HOME, then pairs; beyond = TB (dead marker)."""
    cells = {0: HOME}
    for j, b in enumerate(bits):
        cells[1 + 2 * j] = TB                       # trails: filled below
        cells[2 + 2 * j] = B1v if b else B0v
    cells[1 + 2 * len(bits)] = TB                   # the dead region
    return cells


def main():
    bits0 = [bit_at(j) for j in range(NB)]
    bad = 0
    tot = 0
    # sweep: every pos, every carried d: one cycle, full layout check
    for pos in range(NB):
        for dd in (0, 1):
            if pos == 0 and dd == 1:
                continue                            # no left of pair 0
            if pos == NB - 1 and dd == 0:
                continue                            # no right past horizon
            cells = build_layout(bits0)
            for j in range(pos):
                cells[1 + 2 * j] = TM
            exp_b = bits0[pos]
            exp_pos = pos + 1 if dd == 0 else pos - 1
            park, st = run_machine(cells, 0, f'B0{dd}')
            tot += 1
            if park != f'PB{exp_b}{dd}':
                bad += 1; print(f'  P FAIL pos={pos} dd={dd}: park={park} exp_b={exp_b}')
            for j in range(NB):
                want = TM if j < exp_pos else TB
                if cells[1 + 2 * j] != want:
                    bad += 1; print(f'  T FAIL pos={pos} dd={dd}: pair {j}')
                    break
            if cells[2 + 2 * exp_pos] != (B1v if bits0[exp_pos] else B0v):
                bad += 1; print(f'  D FAIL pos={pos} dd={dd}')
            if cells[0] != HOME:
                bad += 1; print(f'  H FAIL pos={pos} dd={dd}')
            if cells[1 + 2 * NB] != TB:
                bad += 1; print(f'  E FAIL pos={pos} dd={dd}')
    # chaining: every start pos, pseudo-random d, 200 cycles
    for pos in range(NB):
        cells = build_layout(bits0)
        for j in range(pos):
            cells[1 + 2 * j] = TM
        p = pos
        rng = 97531 + pos
        for k in range(200):
            rng = (rng * 1103515245 + 12345) & 0x7fffffff
            dd = (rng >> 16) & 1
            if p == 0 and dd == 1:
                dd = 0
            if p == NB - 1 and dd == 0:
                dd = 1                              # no right past horizon
            exp_b = bits0[p]
            exp_pos = p + 1 if dd == 0 else p - 1
            park, st = run_machine(cells, 0, f'B0{dd}')
            tot += 1
            if park != f'PB{exp_b}{dd}':
                bad += 1; print(f'  CP FAIL chain pos={pos} step {k}: park={park} exp_b={exp_b}')
            for j in range(NB):
                want = TM if j < exp_pos else TB
                if cells[1 + 2 * j] != want:
                    bad += 1; print(f'  C FAIL chain pos={pos} step {k}: pair {j}')
                    break
            p = exp_pos
            if bad > 30:
                print('  ... aborting chain sweep')
                break
        if bad > 30:
            break
    print(f'{tot} cycle cases (sweeps + chains): '
          + ('ALL OK' if bad == 0 else f'{bad} FAILURES'))
    print(f'  phases: {len(T)} defined; machine rows: {sum(len(v) for v in T.values())}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
