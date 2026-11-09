"""gem48x rebuild verifier - the strip-trail footprint rebuild as a MACHINE.

Stage-2 rehearsal of the compiled machine's state-transfer mechanism
(HANDOFF round 17 ledger item 2), implemented as an explicit
(phase, symbol) -> (write, dir, next-phase) table and run by a generic
interpreter, compared exhaustively against an oracle.

GEOMETRY AMEND THIS ROUND (the design fix of the session):
  the STATE CELL is SPLIT from the FOOTPRINT CELL.  The fused single
  cell was unsound twice over: (1) its CUR marker sat on the very cell
  the trips must mark whenever q_new > q_old; (2) its fused pencil leg
  died on the data marker whenever a mark landed at or right of the
  locator.  The sound machine: MID/CUR on their own cells, and every
  trip runs as a hub cycle anchored at HOME, legs in strict order:

      sweep  (once) CUR -> H0 -> erase every SM on the way to HOME
      leg 1  HOME -> CUR:        hop everything right, enter the strip
      leg 2  pencil ONE unit:    (RUNA pencil in run_0 / RUNX->RUNB1 via run_1)
      leg 3  CUR -> HOME:        hop everything left
      leg 4  HOME -> first SB:   mark the frontier (fills 1,2,3,... left to
      ...leg back             right), hop left to HOME, loop leg 1

  The exhaustion cue fires INSIDE the pencil (no extra mark), so the
  mark count equals the pencil count exactly: strips 1..(next_q-1)
  marked, the next unmarked strip's STATE cell gets the CUR
  (first-SB-found).  Halt rows bypass the whole copy (their runs are
  empty AND the class carries the halt flag), so the verifier covers
  the non-halt rows; the halt walk itself is ledger item 3.

ORACLE: the relaid layout with CUR at q_new and SM at j < q_new is
position-identical; every cell (and nothing outside) must match.
Cases: all (q_old, b, q_new) with q_old, q_new in 1..48, b in {0,1}.

Run: py -3.14 < tools/_gem48x_rebuild.py
"""

import sys

(HOME, MID, CUR, SB, SM, HWR, HWL, H1R, H1L, HWRH, HWLH,
 SRC, SP, TBm, TMm, B0v, B1v) = range(17)
H_CLASSES = (HWR, HWL, H1R, H1L, HWRH, HWLH)
NSTRIPS = 48

# ---------------------------------------------------------------- table

T = {}

def row(ph, sym, w, d, nx):
    T.setdefault(ph, {}).setdefault(sym, (w, d, nx))

for b in (0, 1):
    # the ONE-TIME entry: the walker stands on the CUR state cell
    row(f'ENT{b}', CUR, CUR, 1, f'ENF{b}')              # onto the foot cell
    row(f'ENF{b}', SB, SB, 1, f'ENH{b}'); row(f'ENF{b}', SM, SM, 1, f'ENH{b}')
    for h in H_CLASSES:
        row(f'ENH{b}', h, h, -1, f'SAN{b}')             # sweep left from H0
    # the one-time sanitize: erase the entire old footprint
    row(f'SAN{b}', SM, SB, -1, f'SAN{b}')
    for s in (SRC, SP, SB, MID, CUR):
        row(f'SAN{b}', s, s, -1, f'SAN{b}')
    for h in H_CLASSES:
        row(f'SAN{b}', h, h, -1, f'SAN{b}')
    row(f'SAN{b}', HOME, HOME, 1, f'CGO{b}')
    # leg 1, per trip: hop everything right from HOME to the CUR cell
    row(f'CGO{b}', HOME, HOME, 1, f'CGO{b}')
    for s in (MID, SM, SB, SRC, SP):
        row(f'CGO{b}', s, s, 1, f'CGO{b}')
    for h in H_CLASSES:
        row(f'CGO{b}', h, h, 1, f'CGO{b}')
    row(f'CGO{b}', CUR, CUR, 1, f'FENF{b}')             # re-enter, no sweep
    row(f'FENF{b}', SB, SB, 1, f'RH0{b}'); row(f'FENF{b}', SM, SM, 1, f'RH0{b}')
    css = 'RUNX' if b == 1 else 'RUNA'
    for h in H_CLASSES:
        row(f'RH0{b}', h, h, 1, css)                    # step into the half
    # leg 3: the plain hop left back to the hub
    for s in (SRC, SP, SB, SM, MID, CUR):
        row(f'RET{b}', s, s, -1, f'RET{b}')
    for h in H_CLASSES:
        row(f'RET{b}', h, h, -1, f'RET{b}')
    row(f'RET{b}', HOME, HOME, 1, f'TRPM{b}')
    # leg 4: the mark leg anchored at HOME; the frontier fills 1,2,3,...
    row(f'TRPM{b}', HOME, HOME, 1, f'TRPM{b}')
    row(f'TRPM{b}', MID, MID, 1, f'TRPM{b}')
    row(f'TRPM{b}', SM, SM, 1, f'TRPM{b}')
    row(f'TRPM{b}', CUR, CUR, 1, f'TRPM{b}')
    for s in (SRC, SP):
        row(f'TRPM{b}', s, s, 1, f'TRPM{b}')
    for h in H_CLASSES:
        row(f'TRPM{b}', h, h, 1, f'TRPM{b}')
    row(f'TRPM{b}', SB, SM, -1, f'MRET{b}')             # THE mark, step left
    row(f'MRET{b}', SM, SM, -1, f'MRET{b}')
    row(f'MRET{b}', MID, MID, -1, f'MRET{b}')
    row(f'MRET{b}', CUR, CUR, -1, f'MRET{b}')
    for s in (SRC, SP):
        row(f'MRET{b}', s, s, -1, f'MRET{b}')
    for h in H_CLASSES:
        row(f'MRET{b}', h, h, -1, f'MRET{b}')
    row(f'MRET{b}', HOME, HOME, 1, f'CGO{b}')           # completed trip: loop

# the pencil machinery (RH0 steps right off H0 into the half)
for h in H_CLASSES:
    row('RUNA', h, h, 1, 'DONE')                        # run_0 empty/exhausted
row('RUNA', SRC, SP, -1, 'RET0')                        # pencil inside run_0
row('RUNA', SP, SP, 1, 'RUNA')
row('RUNX', SRC, SRC, 1, 'RUNX'); row('RUNX', SP, SP, 1, 'RUNX')  # transit
for h in H_CLASSES:
    row('RUNX', h, h, 1, 'RUNB1')                       # cross into run_1
row('RUNB1', SRC, SP, -1, 'RET1')                       # pencil inside run_1
row('RUNB1', SP, SP, 1, 'RUNB1')
row('RUNB1', MID, MID, -1, 'DONE'); row('RUNB1', TBm, TBm, -1, 'DONE')
row('RUNB1', TMm, TMm, -1, 'DONE')

# the clean+flip pass (the run's exhaustion cue landed here)
row('DONE', SP, SRC, -1, 'DONE')                        # restore the pencils
for s in (SRC, SB, SM, MID):
    row('DONE', s, s, -1, 'DONE')
for h in H_CLASSES:
    row('DONE', h, h, -1, 'DONE')
row('DONE', TBm, TBm, -1, 'DONE'); row('DONE', TMm, TMm, -1, 'DONE')
row('DONE', CUR, MID, -1, 'DONE')                       # the old locator out
row('DONE', HOME, HOME, 1, 'FRS')
row('FRS', MID, MID, 1, 'FRS'); row('FRS', SM, SM, 1, 'FRS')
for s in (SRC, SP):
    row('FRS', s, s, 1, 'FRS')
for h in H_CLASSES:
    row('FRS', h, h, 1, 'FRS')
row('FRS', SB, SB, -1, 'FRS2')                          # the first unmarked foot
row('FRS2', MID, CUR, 1, 'ENDX')                        # the state cell becomes CUR
for s in (CUR, SB, SM, SRC, SP, MID):
    row('ENDX', s, s, 1, 'ENDX')
for h in H_CLASSES:
    row('ENDX', h, h, 1, 'ENDX')
row('ENDX', TBm, TBm, 1, 'ZONE'); row('ENDX', TMm, TMm, 1, 'ZONE')

# ---------------------------------------------------------------- runner

def run_machine(cells, head, phase, max_steps=300_000):
    steps = 0
    ph = phase
    while ph != 'ZONE':
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
    return steps

# ---------------------------------------------------------------- cases

def build_case(cur_q, rows_fn):
    cells = {0: HOME}
    i = 1
    for j in range(1, NSTRIPS + 1):
        cells[i] = CUR if j == cur_q else MID; i += 1
        cells[i] = SM if j < cur_q else SB; i += 1
        for half in (0, 1):
            w, d, nxt = rows_fn(j, half)
            hcls = {(0, 1): HWR, (0, -1): HWL}.get((w, d), H1R if (w, d) == (1, 1) else H1L)
            cells[i] = hcls; i += 1
            for _ in range(max(nxt - 1, 0)):
                cells[i] = SRC; i += 1
    cells[i] = TBm                                        # the stop cue
    return cells


def main():
    def mk(qs, b, qn):
        def rows_fn(j, half):
            if j == qs and half == b:
                return (1, 1, qn)                          # next = qn (never halt)
            return (min(j, 1), 1 if half == 0 else -1, min(j, 3))
        return rows_fn

    used = {nx for ph in T.values() for (_, _, nx) in ph.values() if nx != 'ZONE'}
    unused = set(T) - used - {'ENT0', 'ENT1'}
    total = bad = max_steps = 0
    for q_old in range(1, NSTRIPS + 1):
        print(f'  sweep q_old = {q_old}', flush=True)
        for b in (0, 1):
            for q_new in range(1, NSTRIPS + 1):
                rows_fn = mk(q_old, b, q_new)
                exp = build_case(q_new, rows_fn)
                cells = build_case(q_old, rows_fn)
                cur_pos = next(p for p, v in cells.items() if v == CUR)
                total += 1
                try:
                    st = run_machine(cells, cur_pos, f'ENT{b}')
                    max_steps = max(max_steps, st)
                except AssertionError as exc:
                    bad += 1
                    if bad <= 8:
                        print(f'  FAIL q_old={q_old} b={b} q_new={q_new}: {exc}', flush=True)
                    continue
                if cells != exp:
                    acts = set(cells) ^ set(exp)
                    bad += 1
                    if bad <= 8:
                        print(f'  MISMATCH q_old={q_old} b={b} q_new={q_new}: '
                              f'{[(p, exp.get(p), cells.get(p)) for p in sorted(acts)][:8]}',
                              flush=True)
    print(f'{total} rebuild cases: ' + ('ALL OK' if bad == 0 else f'{bad} FAILURES'),
          flush=True)
    print(f'  phases: {len(T)} defined / {len(used)} referenced '
          f'(unreferenced: {sorted(unused)}); k = 17 symbols; '
          f'max steps on one case: {max_steps}', flush=True)
    print(f'  phase names: {sorted(T)}', flush=True)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
