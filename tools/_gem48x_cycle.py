"""gem48x full-cycle rehearsal (HANDOFF round 16 ledger item 3, parts ii+iii).

One simulated gem48 step as ONE machine cycle, as an explicit
(phase, symbol) -> (write, dir, next) table over the merged layout,
run by a generic interpreter and checked differentially against a
layout oracle.  This stitches the two verified halves together:

  ROUND 17 (trailcheck)  = the trail convention + the +-1 repair;
  ROUND 18 (rebuild)     = the trip protocol rebuilding q -> q_new;
  ROUND 19 (newfetch)    = the head-pair fetch + the b-read;
  THIS ROUND             = all of it inside one cycle, with the
                           (w, d) ROW READ from the strip's H cell,
                           the exec walk writing the sim bit, and
                           the trail repair on the way home.

LAYOUT (the strip REORDERED this round, state cell rightmost --
this is what makes the return crossing able to locate the current
strip by hitting CUR first, and lets the frontier walk stop at the
first unmarked foot without ever entering a strip's interior):

    [HOME] [strip1]...[strip48] [T_1 B_1][T_2 B_2]...[T_NB B_NB] [TBdead]
    strip q =  [foot SB/SM][H0 = row(q,0) class][run0 = qn0-1 SRCs]
               [H1 = row(q,1) class][run1 = qn1-1 SRCs][st MID/CUR]
    data       =  T_i in {TM, TB} (TM iff i < pos; TB = the head's
               own trail cell and the untouched pool beyond);
               B_i in {B0v, B1v} (the sim bits, blank = 0)
    H class    =  H0R/H0L/H1R/H1L (the (w,d) of the non-halt rows)
                  + H0RH/H0LH/H1RH/H1LH (the halt-flagged rows; the
                  halt WALK is a separate follow-up, the classes
                  exist and are hopped over wherever they appear on
                  a crossing, but are not exercised by this battery)

CYCLE (one sim step, from HOME, phase BEG, stateless between
cycles -- only the phase flow; every carry is re-read from tape):

  1. FETCH (H1): walk right.  affiliates: MID/feet/H classes/runs
     kept; SM -> SB ERASED on the way (the one-time sanitize is
     ABSORBED into this crossing); at the data pairs: TM/B hops;
     the FIRST TB = the head's own trail cell -> step right = the
     head pair's data cell; DBIT reads b = the runner-peek (ONE
     cell); walks left back to HOME (CLB, per-b copies), b ridden.
  2. TRIKE (round 18's protocol, mirrored for the reorder):
     CGO_b walks right from HOME to the CUR (passes strip q_old's
     interior); PEN_x walk LEFT off the state cell into run_b
     (b=1: run1 is adjacent; b=0 hops run1 and H1 first), pencil
     the first SRC (the run's rightmost unpencilled cell; the SPs
     form the right-consecutive block), RET_b walk left back to
     HOME, TRPM_b mark the first unmarked foot (the frontier fills
     1,2,3,...), MRET_b back to the hub; the exhaustion cue fires
     when the pencil walk hits the run's boundary class with no SRC
     ahead, skipping pencil+mark exactly: the mark count = the
     pencil count = qn-1.  DONE (the clean+flip): restore SP->SRC
     rightward, erase the OLD CUR (st -> MID), FRS find the first
     SB rightward (strip q_new's foot: strips q_old+1..q_new-1 are
     SM), step right off it and write the NEW CUR there (FRS2).
  3. ROW READ (RR_b): walk LEFT from the new CUR to strip q_old and
     read the b-selected H class there (b=1: at H1; b=0: hop it and
     read at H0).  The class carries (w, d, halt?) -> the walker
     turns around in one of 4 EXEC_{w,d} phase classes, or (halt
     classes) would turn into the halt walk (stub; not exercised).
  4. EXEC (EXW_{w,d}): walk right to the head pair (everything
     hopped); at the head pair's data cell WRITE the sim bit w
     (B0v<-w=0, B1v<-w=1); step left onto the head's own trail
     cell and apply the trail repair per d (FIX_0=d+1: TM at the
     old boundary; FIX_1=d-1: keep TB, write TB at the PREVIOUS
     pair's trail); PHM walks left to HOME; park = BEG: the cycle
     closed.  The head convention is exactly the round-17 one.

STATELESSNESS: nothing carried across cycles (b, w, d, halt all
re-read fresh each cycle).

The BATTERY varies every case: q_old in 1..48 x b in {0,1} x
q_new in 1..48 x (w,d) = 18432 cycles, against the merged oracle:
the strip section must equal the round-18 relaid layout for
q_new (position-identical, nothing outside touched), the data
pair's head bit must equal w, the trail must satisfy the
convention at pos+d, and every other cell byte-for-byte.

Run: py -3.14 < tools/_gem48x_cycle.py
"""

import sys

# strip/marker alphabet
(HOME, MID, CUR, SB, SM, H0R, H0L, H1R, H1L,
 H0RH, H0LH, H1RH, H1LH, SRC, SP, TM, TB, B0v, B1v) = range(19)
H_CLASSES = (H0R, H0L, H1R, H1L, H0RH, H0LH, H1RH, H1LH)
HALT_CLASSES = {H0RH: (0, 1), H0LH: (0, -1), H1RH: (1, 1), H1LH: (1, -1)}
ROW_CLASS = {(0, 1): H0R, (0, -1): H0L, (1, 1): H1R, (1, -1): H1L}
NSTRIPS = 48
NB = 8                                     # data pairs laid in the rehearsal

T = {}

def row(ph, sym, w, d, nx):
    T.setdefault(ph, {}).setdefault(sym, (w, d, nx))


def exname(w, d):
    """Phase name for the (w, d) exec-carry quadruple."""
    return f'EXW{w*2 + (1 if d == -1 else 0)}'

HOP_R = (MID, CUR, SB, SRC, SP, B0v, B1v)
HOP_L = (MID, CUR, SB, SB, SM, SRC, SP, B0v, B1v, TB, TM)

# ---- 1. the fetch (BEG/H1/DBIT/CLB) ----
row('BEG', HOME, HOME, 1, 'H1')
row('H1', TM, TM, 1, 'H1')
for s in (MID, CUR, SB, SRC, SP, B0v, B1v):
    row('H1', s, s, 1, 'H1')
row('H1', SM, SB, 1, 'H1')                       # the sanitize absorbed here
for h in H_CLASSES:
    row('H1', h, h, 1, 'H1')
row('H1', TB, TB, 1, 'DBIT')                     # first TB = the head
row('DBIT', B0v, B0v, -1, 'CLB0'); row('DBIT', B1v, B1v, -1, 'CLB1')
for b, ph in ((0, 'CLB0'), (1, 'CLB1')):
    for s in (TM, TB, B0v, B1v, MID, SB, SM, CUR, SRC, SP):
        row(ph, s, s, -1, ph)
    for h in H_CLASSES:
        row(ph, h, h, -1, ph)
    row(ph, HOME, HOME, 1, f'CGO{b}')

# ---- 2. the trike (CGO/PEN_x/RET/TRPM/MRET/DONE/FRS/FRS2) ----
for b in (0, 1):
    row(f'CGO{b}', HOME, HOME, 1, f'CGO{b}')
    for s in (MID, SB, SM, SRC, SP):
        row(f'CGO{b}', s, s, 1, f'CGO{b}')
    for h in H_CLASSES:
        row(f'CGO{b}', h, h, 1, f'CGO{b}')
    row(f'CGO{b}', CUR, CUR, -1, f'PEN{b}')      # arrive: walk left into runs

row('PEN0', SRC, SRC, -1, 'PEN0')                # cross run1 for b=0
for h in H_CLASSES:
    row('PEN0', h, h, -1, 'PEN00')               # H1 crossed = enter run0
row('PEN00', SRC, SP, -1, 'RET0')                # THE pencil in run0
row('PEN00', SP, SP, -1, 'PEN00')
for h in H_CLASSES[:4]:
    row('PEN00', h, h, 1, 'DONE')                # exhaust cue at H0-class
for h in H_CLASSES[4:]:
    row('PEN00', h, h, 1, 'DONE')

row('PEN1', SRC, SP, -1, 'RET1')                 # run1 adjacent: straight in
row('PEN1', SP, SP, -1, 'PEN1')
for h in H_CLASSES:
    row('PEN1', h, h, 1, 'DONE')                 # exhaust cue at H1-class

for b in (0, 1):
    for s in (SRC, SP, SB, SM, MID, CUR):
        row(f'RET{b}', s, s, -1, f'RET{b}')
    for h in H_CLASSES:
        row(f'RET{b}', h, h, -1, f'RET{b}')
    for s in (TM, TB, B0v, B1v):
        row(f'RET{b}', s, s, -1, f'RET{b}')
    row(f'RET{b}', HOME, HOME, 1, f'TRPM{b}')
    # leg 4: the mark leg anchored at HOME; frontier fills 1,2,3,...
    row(f'TRPM{b}', HOME, HOME, 1, f'TRPM{b}')
    row(f'TRPM{b}', MID, MID, 1, f'TRPM{b}')
    row(f'TRPM{b}', SM, SM, 1, f'TRPM{b}')
    row(f'TRPM{b}', CUR, CUR, 1, f'TRPM{b}')
    row(f'TRPM{b}', SB, SM, -1, f'MRET{b}')      # THE mark, step left
    row(f'MRET{b}', SM, SM, -1, f'MRET{b}')
    row(f'MRET{b}', MID, MID, -1, f'MRET{b}')
    row(f'MRET{b}', CUR, CUR, -1, f'MRET{b}')
    row(f'MRET{b}', HOME, HOME, 1, f'CGO{b}')

# the clean+flip: restore the pencils rightward, erase the OLD CUR
row('DONE', SRC, SRC, 1, 'DONE')
row('DONE', SP, SRC, 1, 'DONE')
for h in H_CLASSES:
    row('DONE', h, h, 1, 'DONE')                 # cross to the other run
row('DONE', CUR, MID, 1, 'FRS')                  # the old locator out
row('FRS', MID, MID, 1, 'FRS'); row('FRS', SM, SM, 1, 'FRS')
for s in (SRC, SP):
    row('FRS', s, s, 1, 'FRS')
for h in H_CLASSES:
    row('FRS', h, h, 1, 'FRS')
row('FRS', SB, SB, 1, 'FRS20'); row('FRS', SB, SB, 1, 'FRS21')  # (b copies)
row('FRS20', MID, CUR, -1, 'RR0'); row('FRS21', MID, CUR, -1, 'RR1')

# ---- 3. the row read (RR_b): left to q_old, read the b-side class ----
for b in (0, 1):
    ph = f'RR{b}'
    row(ph, CUR, CUR, -1, ph)                    # step left off the new CUR
    for s in (SRC, SP, SB, SM, MID):
        row(ph, s, s, -1, ph)
    if b == 1:
        for (wd, hc) in ROW_CLASS.items():      # the H1 = the selected read
            row(ph, hc, hc, 1, exname(wd[0], wd[1]))
        for hc in HALT_CLASSES:
            row(ph, hc, hc, 1, 'HALTX')          # halt walk: NOT exercised
    else:
        for (wd, hc) in ROW_CLASS.items():       # b=0: H1 crossed first
            row(ph, hc, hc, -1, ph)
        for (wd, hc) in ROW_CLASS.items():
            row(ph, hc, hc, 1, exname(wd[0], wd[1]))
        for hc in HALT_CLASSES:
            row(ph, hc, hc, 1, 'HALTX')

# ---- 4. the exec (EXW_{w,d} -> the trail repair -> PHM -> BEG) ----

for w in (0, 1):
    for d in (1, -1):
        ph = exname(w, d)
        for s in (MID, SB, SM, SRC, SP):
            row(ph, s, s, 1, ph)
        for h in H_CLASSES:
            row(ph, h, h, 1, ph)
        for s in (TM, B0v, B1v):
            row(ph, s, s, 1, ph)
        # crossed strips' states are MID; no CUR remains
        row(ph, TB, TB, 1, ph + 'W')             # first TB = the head
        row(ph + 'W', B0v, B1v if w == 1 else B0v, -1, f'FIX{d}')
        row(ph + 'W', B1v, B1v if w == 1 else B0v, -1, f'FIX{d}')
row('FIX1', TB, TM, -1, 'PHM')                   # d=+1: clear old boundary
row('FIX-1', TB, TB, -1, 'FIXM')                 # d=-1: keep; move left
row('FIXM', TM, TB, -1, 'PHM')                   # mark the new boundary
for s in (TM, TB, B0v, B1v, MID, SB, SM, CUR, SRC, SP):
    row('PHM', s, s, -1, 'PHM')
for h in H_CLASSES:
    row('PHM', h, h, -1, 'PHM')
row('PHM', HOME, HOME, 1, 'BEG')                 # the cycle closes

# ---------------------------------------------------------------- runner

def run_machine(cells, head, phase, max_steps=1_000_000):
    steps = 0
    ph = phase
    while ph != 'BEG':
        r = T[ph].get(cells[head])
        if r is None:
            raise AssertionError(f'death: {ph} on symbol {cells[head]} at {head}')
        w, d, nx = r
        if w is None:
            raise AssertionError(f'halt-class fired at {ph}')
        cells[head] = w
        head += d
        ph = nx
        steps += 1
        if steps > max_steps:
            raise AssertionError('budget')
    return steps


# ---------------------------------------------------------------- harness

def build_case(cases):
    """(q_cur, rows_fn, bits, head) -> cells dict + cur position."""
    q_cur, rows_fn, bits, head = cases
    cells = {0: HOME}
    i = 1
    for j in range(1, NSTRIPS + 1):
        st, f0, r0, f1, r1 = rows_fn(j)
        cells[i] = SB; i += 1                    # foot = SB in this builder
        cells[i] = f0; i += 1
        cells[i] = r0; i += 1
        cells[i] = f1; i += 1
        cells[i] = r1; i += 1
        cells[i] = CUR if j == q_cur else MID; i += 1
    for k in range(1, NB + 1):
        cells[i] = TM if k < head else TB; i += 1
        if k == head and head <= len(bits):
            cells[i] = B1v if bits[head - 1] else B0v; i += 1
        else:
            cells[i] = B1v if bits[k - 1] else B0v; i += 1
    cells[i] = TB                                # the pool's right end
    return cells, i - (NB - head) - 2            # the head's trail cell? no


def footprint_oracle(q_new):
    """The round-18 relaid layout oracle for the strip section."""
    pass                                          # (filled in main below)


def main():
    total = bad = max_steps = 0
    for q_old in range(1, NSTRIPS + 1):
        print(f'  sweep q_old = {q_old}', flush=True)
        for b in (0, 1):
            for qn in range(1, NSTRIPS + 1):
                for (w, d) in ((0, 1), (0, -1), (1, 1), (1, -1)):
                    def rows_fn(j):
                        if j == q_old:            # no: checked below
                            pass
                        # strip j: [SB, H0, run0, H1, run1, state]
                        if j == q_old and b == 0:
                            h0, r0len = ROW_CLASS[(w, d)], max(qn - 1, 0)
                            h1, r1len = ROW_CLASS[(min(j, 2), 1)], max(min(j, 3) - 1, 0)
                        elif j == q_old and b == 1:
                            r0len = max(min(j, 3) - 1, 0)
                            h1, r1len = ROW_CLASS[(w, d)], max(qn - 1, 0)
                        else:
                            r0len = max(min(j, 3) - 1, 0)
                            h1, r1len = ROW_CLASS[(min(j, 2), 1)], max(min(j, 3) - 1, 0)
                        h0 = ROW_CLASS[(0, 1)] if j != q_old or b != 0 else ROW_CLASS[(w, d)]
                        return [SB, h0, r0len, h1, r1len]
                    total += 1
                    try:
                        # build + run + diff against the merged oracle
                        raise AssertionError('harness skeleton: not yet wired')
                    except AssertionError as exc:
                        bad += 1
                        if bad <= 8:
                            print(f'  harness: {exc}', flush=True)
    print(f'{total} cycle cases: ' + ('ALL OK' if bad == 0 else f'{bad} FAILURES'),
          flush=True)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
