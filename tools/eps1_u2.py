"""eps1_u2.py — the U2 rewrite DRAFT.  HALTED 2026-11-04, before any
gate ran: the fork-wall argument kills this redesign too.

The verdict, by argument (four derivations this turn, consistent with
all three recorded merge hunts): every p-split arm ends its park visit
with a rightward walk whose landing action differs by route (plain
pred / fs push / absorb pop / widen), and no tape cell the walk passes
can carry the case bit.  The sep cells are 00 (decode's park count
stops at the first 0 after C0-3); the terminator pair's cells are 0 and
must be; end+1 is blank but off the walk; the sentinel proposal (a
non-zero cell past the last close) is eaten by decode_tape's run
counting and misread as the next entry's first mark.  So the redesign's
own returns fork exactly like eps1_odi's do, and the honest state
forecast lands in the same 71-adjacent band as the shipped 71 / 72 / 76.
This file stays as the design draft + the blocked evidence, not a
bearing build.  See HANDOFF.md round 10 for the full argument.

The original draft text, kept for the record:

Goal: sn=1 under 67 states (the record is 71 in eps1_odi.py), by
removing the duplicated per-arm long walks.  Everything else is
identical on purpose: same tape format, same model (eps1_chain.step at
the fixed seed sn), same campaign contract (one C.step per rest-to-rest
campaign, one move counted per campaign, machine death on the empty
dispatch the same way).

TAPE — unchanged from eps1_odi:

    [1^p park] 0 0 [1^L1 0][1^L2 0]...[1^Lk 0] [0] [0 0 0 ...]

park right end at C0-3, sep (C0-2, C0-1), chain from C0, top run the
RIGHTMOST (machine launches on it), rest head on its last mark E.

MODEL ACTIONS (from tools/eps1_chain.py, fixed seed sn):
  top entry (numeral c >= 2 or an ordinal bot): succ value:
    p == 0: PRED  : top c -> c-1; c==1 -> empty (halt next; the machine
                    performs the erase and the empty dispatch dies).
    p >= 1: FS    : top c -> c-1, PUSH ORD NUM(sn+1) of sn+3 marks after
                    it, p -= 1.  (ATOM1 top: top stays [ATOM], push.)
  top = ATOM (eps_0, L=1): limit: entry widens to NUM(1) (L=3) and
                    p += sn (the fs-limit arm, p-independent).
  top = NUM(1)-ord (L=3) with m==1 (no entry below):
    p == 0: top -> empty (HALT-NEXT; erase + rest, the next dispatch
                    dies = the final move).
    p >= 1: FS on the numeral top: entry -> NUM(sn+1) (L=sn+3), p -= 1:
                    'head-empty rewrite' (erase the 3 old marks, write
                    sn+3 fresh, NO push: the entry stays alone).
  top = NUM(1)-ord with an entry below: impossible (GU; machine death).

U2 GEOMETRY — every arm runs
  [E-zone p-independent part] -> [left ride to the park (WAD-shape, one
  shared rider family)] -> [the LOOK at C0-3 (a small clone family: the
  p0 arm differs per route, the p>=1 arm is the fs spend for all
  fs-shaped routes)] -> [park part] -> [right return (the shared ride
  with the 00-disambiguator, family's 0-arm wired per arm)] -> [the
  E-zone push part when p>=1] -> [BR, the shared walk home, 5 states].

The old per-arm right-walk families (WBX/WB_P, WR_FS, WB_ABS, WR_A;
~21 states on sn=1) and the per-route walk-to-look clones collapse
into the shared riders.  The cascade keeps its whole geometry (the
park stays at C0-3).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import eps1_chain as C
from eps1_odi import (mk_tape, decode_tape, campaign, step_model,
                      census_battery, check_moves_random, check_tiers)
import eps1_odi


def build_table(sn):
    """Rows: state -> {read: (w, d, nxt)}; a missing row = death."""
    T = {}
    meta = {}

    def add(name, note):
        assert name not in T, f'duplicate {name}'
        T[name] = {}
        meta[name] = note

    def row(name, sym, w, d, nxt):
        T[name][sym] = (w, d, nxt)

    # ---- DISPATCH (at E, the top run's last mark) --------------------
    # reads E-1, E-2, ...: the top run's marks right-to-left; the m
    # tests read one cell past the run, into the entry below the top.
    # Arms fire at various E-k and then all route into the shared LEFT
    # rider (the park visit) or straight into the shared fs shape.
    add('IN', 'rest dispatch')
    row('IN', 1, 1, 'L', 'D2')
    add('D2', 'read E-1: 0 = L==1 (atom, route A), else continue')
    row('D2', 1, 1, 'L', 'D3')
    add('D3', 'read E-2: 0 = L==2 (ATOM1; route B), else continue')
    row('D3', 1, 1, 'L', 'D4')
    add('D4', 'read E-3: 0 = L==3, else continue')
    row('D4', 1, 1, 'L', 'D5')
    add('D5', 'read E-4: 0 = L==4, else L>=5 (route E)')
    row('D5', 1, 1, 'L', 'WAD')        # route E: straight to the park visit
    add('M4', "L==4 m-test at E-5: 1 = lower run (m>=2), 0 = bottom (m==1)")
    row('M4', 0, 0, 'L', 'WAD')        # route D-m1: to the park visit
    row('M4', 1, 1, 'L', 'WAD')        # route D-m2: to the park visit
    # route B/L2 arm and route C/L3 arm fire from the dispatch zone and
    # are filled in below (the L2 arm is p-split at this point: p0 =
    # plain pred (no push), p>=1 = fs).

    # ---- shared left rider (anywhere on the chain right of the park)
    # rides left over 1s, crosses 0s, and resolves the sep 00: after the
    # second 0 the next read is the park's right end C0-3 = the LOOK.
    add('WAD', 'left rider: over the chain; 0 = crossed the first cell')
    row('WAD', 1, 1, 'L', 'WAD')
    row('WAD', 0, 0, 'L', 'WAZ')
    add('WAZ', "left rider: second cell (an entry's mark, or the sep's tail)")
    row('WAZ', 1, 1, 'L', 'WAD')
    row('WAZ', 0, 0, 'L', 'LOOK')      # the sep crossed: the park cell

    # ---- the LOOK at C0-3.  Clones: the p1 arm is the fs spend for the
    # fs-shaped routes (B-m1, B-m2, D-m1, D-m2, E); the p0 arm differs.
    add('LOOK_F', 'fs-shaped look (L2/L4/L>=5 routes): p>=1 = fs, extend')
    row('LOOK_F', 1, 1, 'L', 'FSL')    # p >= 1: walk left over the park
    row('LOOK_F', 0, 0, 'R', 'HR')     # p == 0: plain pred body already
                                       # done at the dispatch zone; home.
    add('LOOK_C', "L3 m==1 look: p==0 = the halting pred, p>=1 = head-empty")
    row('LOOK_C', 1, 1, 'L', 'FSL')    # p >= 1: the head-empty is pure fs:
                                       # spend, then rewrite in place.
    # p == 0: NO ROW (death) = the final-move contract.
    # route A (L==1) never looks: the arm is p-independent.

    # ---- the fs spend (leftmost-mark erase): shared by every fs arm
    add('FSL', 'fs spend: left over the park marks to the first blank')
    row('FSL', 1, 1, 'L', 'FSL')
    row('FSL', 0, 0, 'R', 'FSP')
    add('FSP', 'fs spend: erase the leftmost park mark, step right')
    row('FSP', 1, 0, 'R', 'FSR1')

    # ---- the fs right return: from the park's left-1 to the push zone.
    # Rides right over the park, the sep (00), and the chain; the FIRST
    # 00 triplets: after the sep the NEXT read is always 1 (chain), so
    # the continuation row covers the sep crossing; the return ends at
    # the terminator 00, backs up 2 onto the new close, and enters the
    # append write chain at the old close cell E+1.
    add('FSR1', 'fs return: ride right (park marks / chain marks)')
    row('FSR1', 1, 1, 'R', 'FSR1')
    row('FSR1', 0, 0, 'R', 'FSR2')
    add('FSR2', 'fs return: one 0 crossed (a close or the sep front)')
    row('FSR2', 1, 1, 'R', 'FSR1')
    row('FSR2', 0, 0, 'R', 'FSR3')
    add('FSR3', 'fs return: second 0 (sep tail or terminator)')
    row('FSR3', 1, 1, 'R', 'FSR1')     # sep: the chain follows
    row('FSR3', 0, 0, 'L', 'FSR4')     # terminator: back up
    add('FSR4', 'fs return: at the terminator tail, step left')
    row('FSR4', 0, 0, 'L', 'FSR5')
    row('FSR4', 1, 0, 'L', 'FSR5')
    add('FSR5', 'fs return: land the head on the old close (E+1)')

    # ---- route A (L==1): p-independent: widen the run 1->3 and extend
    # the park by sn marks.  Widen rows hang on the dispatch arm; the
    # extension walks left (WAD), then rides the park to the blank and
    # writes sn marks, one write-state per mark; then walks home.
    # (the widen's writes: at the explicit site, then the left rider
    # starts from the widened close's left neighbour = still inside the
    # chain, so WAD is entered mid-chain (its 0-arm arms the sep).)
    if sn >= 2:
        for j in range(2, sn + 1):
            add(f'PE{j}', f'route A extend: write mark {j} of {sn}')
            row(f'PE{j}', 0, 1, 'L', 'BR' if j == sn else f'PE{j}' + 'X')
    # the PE chain is filled conditionally below (sn=1 needs none).

    # ---- walk home (shared, arrives from anywhere left of the chain):
    # rides right over the sep/chain to the terminator, backs up 2 onto
    # the top run's last mark, and dispatches.
    add('BR', 'walk home right')
    row('BR', 1, 1, 'R', 'BR')
    row('BR', 0, 0, 'R', 'BRZ')
    add('BRZ', 'walk home: crossed a 0')
    row('BRZ', 1, 1, 'R', 'BR')
    row('BRZ', 0, 0, 'R', 'BRQ')
    add('BRQ', 'walk home: pair test (sep or terminator?)')
    row('BRQ', 1, 1, 'R', 'BR')
    row('BRQ', 0, 0, 'L', 'BRH1')
    add('BRH1', 'walk home: at terminator tail, back up 1')
    row('BRH1', 0, 0, 'L', 'BRH2')
    row('BRH1', 1, 0, 'L', 'BRH2')
    add('BRH2', 'walk home: land the head on the top mark, state IN')
    row('BRH2', 0, 0, 'L', 'IN')
    row('BRH2', 1, 0, 'L', 'IN')

    # ---- append machinery (the fs push, from the old close cell E+1):
    # FSR5 enters it at the old close; the chain writes sn+3 marks and
    # the close write rests IN (one campaign ends; next fires fresh).
    add('APW0', 'append bridge: at the old close cell')
    row('APW0', 0, 0, 'R', f'A{sn+3}')
    row('APW0', 1, 1, 'R', 'APW0')     # defensive
    for k in range(sn + 3, 0, -1):
        add(f'A{k}', f'append: write mark ({sn+3-k+1} of {sn+3})')
        if k == 1:
            row(f'A{k}', 0, 1, 'R', 'BR')    # marks done; the head is at
            row(f'A{k}', 1, 1, 'R', 'BR')    # the new close cell; walk home
        else:
            row(f'A{k}', 0, 1, 'R', f'A{k-1}')
            row(f'A{k}', 1, 1, 'R', f'A{k-1}')

    # the minimise pass of record
    T, meta = eps1_odi.minimise_table(T, meta, 'IN')
    return T, meta


def main():
    failed = 0
    for sn in (1,):
        T, meta = build_table(sn)
        ok, bad, halts, failures = census_battery(T, sn)
        print(f'sn={sn}: states={len(T)} rows={sum(len(r) for r in T.values())} '
              f'gate1 census ok={ok} bad={bad} halts={halts}')
        for f in failures[:14]:
            print('   FAIL', f)
        if bad:
            failed += 1
        if check_tiers(T, sn):
            failed += 1
    print('ALL OK' if failed == 0 else f'{failed} GATE FAILURES')
    sys.exit(0 if failed == 0 else 1)


if __name__ == '__main__':
    main()
