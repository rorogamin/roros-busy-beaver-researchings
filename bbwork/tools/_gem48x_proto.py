"""gem48x prototype — the SHUTTLE interpreter of gem48 (stage 1: harness + plan).

What this file IS tonight (honest):
  * the gem48 loader + direct-sim oracle (verified against the repo's
    recorded facts) = the baseline EVERY transcription of the compiled
    machine will be differential-checked against, and
  * the PHASE PLAN OF RECORD for the compiled machine, counted
    honestly (phases x symbols), committed so the transcription
    session starts from a frozen geometry.

What it is NOT yet: the compiled machine's transition table itself
(ether: the machine body below, stage 2).

DESIGN OF RECORD (HANDOFF round 15): shuttle/fetch-execute family.
  M  = gem48 (48 states, 2 symbols, morphett gem48_morphett.txt).
  Mx = compiled: sim state q lives on the TAPE (the strip-trail
       footprint + the state strips), the compiled control = fixed
       phase set independent of |Q(M)|, k symbols, polynomial
       slowdown accepted (the transcendence claim only gets STRONGER).

LAYOUT (betas of the frozen geometry):

    [HOME barrier]  [strip 1] ... [strip 48]   [data pairs: [T_i][B_i] ...]

      strip q      =  [SM/SB(q)]  [H(q,0)]  [source run f(q,0)]  [H(q,1)]  [source run f(q,1)]
      SM / SB      =  the strip-trail cell: marked (SM) iff strip j < q
                      (the CURRENT q footprint, read-scan; repaired +-1 per step)
      H(q,b)       =  one of 4 symbols HWR/HWL/H1R/H1L encoding (w,d) of row (q,b)
      source run   =  f(q,b): the NEXT-state count, one SR per unit
                      (read-only; pencilled SP during the copy; restored)
      data pair i  =  [T_i] = trail cell (TM iff j < pos), [B_i] = sim bit B0/B1
      HOME         =  the left barrier (the walker's left stop cue)

CYCLE (one simulated gem48 step; rest = at the sim head pair's trail cell):
  1. FS   : fetch walk right through the strips; SM -> hop; SB -> the
            current strip; from there: read the b-selected row cell
            (carry (w,d) in 4 phase classes, b-select via 2 classes).
  2. COPY : rebuild the strip-trail footprint q := q' by the
            pencil-copy: per source SR of f(q,b): walk to the
            frontier (+/- fix), place one footprint mark; pencil each
            consumed SR (SR->SP) and restore the run at the end.
  3. EXEC : walk right to the data head; write the row's w on the sim
            bit; apply the +-1 trail fix (d=R: mark the head pair's
            own trail cell; d=L: unmark the previous pair's trail);
            rest at the new head pair's trail cell.
  HALT    : the row's next = halt -> a dedicated halt walk (the compiled
            machine stops; the move/step parity of record follows).

FROZEN COUNT ESTIMATE (the number the transcription session is held to):
  phases (before the b-carry x d-carry expansion): 11 named families
  below; with the honest expansion the target stays below 48 compound
  states, and the run's step factor is O(strip distance) per sim step.

Run: py -3.14 < tools/_gem48x_proto.py
"""

import os, sys, time


def find_project_root():
    """Walk up from the cwd (stdin runs have __file__ = '<stdin>')."""
    here = os.path.abspath(os.getcwd())
    for d in (here, os.path.dirname(here)):
        if os.path.isfile(os.path.join(d, 'gem48_morphett.txt')):
            return d
    return here


ROOT = find_project_root()

# ---------------------------------------------------------------- the loader

def load_gem48(path=None):
    """gem48_morphett.txt -> T[q][b] = (w, d, nxt|None).  q in 0..47
    (morphett S01->0..S48->47), b in {0,1} ('_' = 0), nxt None = halt."""
    if path is None:
        path = os.path.join(ROOT, 'gem48_morphett.txt')
    if not os.path.isfile(path):
        path = os.path.join(ROOT, 'gem48_morphett.txt')
    T = {}
    with open(path, 'r') as fh:
        for ln in fh:
            ln = ln.strip()
            if not ln or ln.startswith(';'):
                continue
            st, rd, w, mv, nxt = ln.split()
            q = int(st)
            b = 0 if rd == '_' else int(rd)
            wv = 0 if w == '_' else int(w)
            d = 1 if mv == 'r' else -1
            nx = None if nxt == 'halt' else int(nxt)
            T.setdefault(q, {})[b] = (wv, d, nx)
    return T


# ---------------------------------------------------------------- the oracle

def gem48_run(T, max_steps=2_000_000, start_tape=None, state=0, head=0):
    """Direct blank-tape run of M from state `state`.  Blank run of
    record: no halt in 2M steps.  Returns (halted, steps, cells, pos)."""
    cells = dict(start_tape or {})
    pos, q, steps = head, state, 0
    while steps < max_steps:
        row = T.get(q, {}).get(cells.get(pos, 0))
        if row is None:                      # missing row = halt
            return True, steps, cells, pos
        w, d, nxt = row
        if w == 0:
            cells.pop(pos, None)             # keep the dict sparse
        else:
            cells[pos] = 1
        pos += d
        q = nxt
        if q is None:                        # an explicit halt row spent: M halts
            return True, steps + 1, cells, pos
        steps += 1
    return False, steps, cells, pos


# ---------------------------------------------------------------- the plan

PHASE_FAMILIES = [
    ('FS',    'strip fetch walk right (SM hop, SB = the current strip)', 1),
    ('HS0',   'strip enter: cross to H(q,0) and read (b=0 branch)',      1),
    ('HS1',   'strip enter: cross half-0 field, read H(q,1) (b=1 branch)', 1),
    ('COPYR', 'pencil-trip right: cross slot/strip cells to the frontier', 1),
    ('COPYW', 'frontier fix: place one footprint mark on the next-j strip', 3),
    ('CLEANP','restore pencilled SRs (SP->SR) walking left',               1),
    ('EXECR', 'walk right to the data head (over TM pairs)',              1),
    ('EX0R',  'execute classes (w,d carried, 4) at the sim head bit',      4),
    ('TRFIX', 'the +-1 trail fix (d=R: mark own trail; d=L: unmark prev)', 2),
    ('GHLT',  'the halt walk (the row targeted halt; stop clean)',         1),
    ('BOOTL', 'the interpreter boot writer (ledger item, not counted in the compound)', 0),
]

SYMBOLS = [
    ('HOME', 'left barrier'), ('B0', 'sim bit 0'), ('B1', 'sim bit 1'),
    ('TB', 'data trail unmarked'), ('TM', 'data trail marked'),
    ('SB', 'strip trail unmarked (>= q)'), ('SM', 'strip trail marked (< q)'),
    ('HWR', 'row cell (w=0,d=r)'), ('HWL', 'row cell (w=0,d=l)'),
    ('H1R', 'row cell (w=1,d=r)'), ('H1L', 'row cell (w=1,d=l)'),
    ('SR', 'source mark (next-q unit)'), ('SP', 'pencilled source mark'),
    ('SE', 'strip-area empty/distance cell'),
]

# ---------------------------------------------------------------- main

def main():
    T = load_gem48()
    nstates = len(T)
    rows = sum(len(r) for r in T.values())
    halt_rows = sorted((q, b) for q in T for b in T[q] if T[q][b][2] is None)
    print(f'gem48 loaded: {nstates} states, {rows} rows, halt rows at {halt_rows}')
    ok = nstates == 48 and rows == 96

    t0 = time.time()
    halted, steps, cells, pos = gem48_run(T, max_steps=2_000_000)
    dt = time.time() - t0
    print(f'  blank run 2M: halted={halted} steps={steps} '
          f'cells={len(cells)} head={pos} ({dt:.1f}s)')
    ok = ok and (not halted) and steps == 2_000_000

    nfam = sum(c for _, _, c in PHASE_FAMILIES[:9])
    print(f'  phase plan of record: {len(PHASE_FAMILIES)} families, '
          f'{nfam} phase classes before the honest b-carry x d-carry expansion; '
          f'k = {len(SYMBOLS)} symbols')
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
