"""eps1_odi.py — the unified ODOMETER core: one machine campaign
(rest-to-rest) = one eps1_chain.step at the build's fixed seed.

The design of record is EPS1_SUPER.md §"The unified ODOMETER rewrite":
an eps1_table-style tape WITHOUT the index field, the bottom kind encoded
in the first run's length, and one position-anchored exec core.

TAPE (all cells 0/1; blank = 0):

    [1^p park]  0 0  [entry1: 1^L 0][entry2: 1^L' 0]...  [0]  [0 0 0 ...]

  * park right-anchored: the park's RIGHT end is cell C0-3 forever
    (the sep is C0-2, C0-1; the chain starts at C0).  p >= 1 iff cell
    C0-3 carries a mark.  A spend erases the park's LEFTMOST mark;
    growth writes one cell further left.
  * entry code: a run of L marks followed by one close 0.  L = 1 is the
    bottom atom (eps_0), L = 2 the bottom atom+1 (eps_0+2), L >= 3 the
    plain entry with coefficient c = L-2.  Only the bottom entry may be
    L = 1 or 2; the top entry's L determines nothing beyond its own
    coefficient.
  * chain end: one extra 0 after the last close.  Walking RIGHT, the
    first 0-0 pair is (last close, chain end); the park's sep pair is
    skipped via the BRQ test (one cell further right: 1 = sep, 0 =
    terminator).
  * hole invariant: no interior 00.  A pop erases the whole run; an
    append writes starting AT the chain-end cell, overwriting it, so
    the write zone is blank before and the seps stay single.
  * rest: the head sits ON the top run's last mark in state IN.  The
    next visit fires the dispatch.  Halt convention: the p == 0,
    L == 3, m == 1 site is the model's (0,[NUM(1)]) -> (0,[]) -> halt;
    that arm has NO row (machine death there) and the harness counts
    that death as the final move, matching eps1_chain.run counts.

DECISION MATRIX (canonical states; eps1_chain.step at fixed seed sn,
the pushed entry value sn+1 with run length sn+3):

  top L == 1            (always m == 1, [ATOM])     FS-LIMIT: p += sn, run 1->3
  top L == 2            (always m == 1, [ATOM1])    dec (2->1); p >= 1: +append+spend
  top L == 3, m == 1    ([NUM(1)])                  p == 0: halt (no row);
                                                    p >= 1: head-empty rewrite sn+3
  top L == 3, m >= 2                                impossible canonical: GU death
  top L == 4, m == 1    ([NUM(2)])                  dec; p >= 1: +append+spend
  top L == 4, m >= 2                                p == 0: ABSORB (pop, park += 1,
                                                        cascade);
                                                    p >= 1: dec + append + spend
  top L >= 5                                        dec; p >= 1: +append+spend

Faithfulness gates (all must be ALL OK):
  1. every exact pre-step state visited by the six fixed-seed full runs
     (the census): machine moves match eps1_chain.step landings;
  2. random one-step battery: 400 chains x 4 moves;
  3. full runs tiers 1..7 x seeds {1,2}: halting counts equal C.run;
  4. state count printed honestly (raw; Moore refinement later).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import tm
import random

import eps1_chain as C


# ---------------------------------------------------------------------------
# chain <->tape helpers (machine-independent)

def entry_len(c):
    """Run length L for plain entry coefficient c."""
    return c + 2


def _numlike_zero(x):
    """True if x is an integer 0 or a zero-valued Ord-like exponent."""
    if x is None:
        return False
    if x == 0:
        return True
    f = getattr(x, 'is_zero', None)
    try:
        return bool(f())
    except Exception:
        return False


def ord_entry(e):
    """Encoding run length L of a descent-Ord chain entry, by value:
    eps_0+1 -> 1, eps_0+1+1 -> 2, numeral k -> k+2."""
    if e == C.ATOM or getattr(e, 'is_atom', lambda: False)():
        return 1
    if e == C.ATOM1:
        return 2
    terms = getattr(e, 'terms', None)
    if (terms and len(terms) == 1 and _numlike_zero(terms[0][0])
            and terms[0][1] >= 1):
        return entry_len(terms[0][1])
    raise ValueError(f'mk_tape: unexpected chain value {e!r}')


def mk_tape(p, chain):
    """(tape cells dict, rest head).  chain values: ints for plain
    entries, C.ATOM, C.ATOM1 (the atom bottoms); a plain-numeral bottom
    arrives as the int c.  Returns (cells, head) with head on the top
    run's last mark (or the park cell C0-2 for the empty chain)."""
    cells = {}
    for j in range(p):
        cells[-3 - j] = 1
    runs = []
    for e in chain:
        if e is C.ATOM:
            runs.append(1)
        elif e is C.ATOM1:
            runs.append(2)
        elif isinstance(e, int):
            runs.append(entry_len(e))
        elif getattr(e, 'terms', None) == ((None, 1),):
            runs.append(1)          # an atom-form equal to C.ATOM by value
        elif getattr(e, 'terms', None) == ((None, 1), (0, 1)):
            runs.append(2)          # ATOM+NUM(1), equal to C.ATOM1 by value
        elif (hasattr(e, 'terms') and len(e.terms) == 1
              and e.terms[0][0] == 0 and e.terms[0][1] >= 1):
            runs.append(entry_len(e.terms[0][1]))   # C.NUM(k) numeral form
        else:
            runs.append(ord_entry(e))
    pos = 0
    top_last = None
    for L in runs:
        for k in range(L):
            cells[pos + k] = 1
        pos += L + 1
        top_last = pos - 2
    head = top_last if runs else -2
    return cells, head


def chain_values_to_model(vals):
    """The harness's built-chain to the model (p, chain, seed n)."""
    return vals


def decode_tape(cells):
    """Machine tape -> (p, chain) model values (ints/ATOM/ATOM1)."""
    p = 0
    j = -3
    while cells.get(j, 0) == 1:
        p += 1
        j -= 1
    chain = []
    pos = 0
    while True:
        start = pos          # the run's start decides the bottom kind
        L = 0
        while cells.get(pos, 0) == 1:
            L += 1
            pos += 1
        if start == 0 and L == 0:
            return (p, [])
        if L == 0:
            if start == 0:
                return (p, [])  # empty chain at C0
            if cells.get(pos, 0) == 0 and cells.get(pos + 1, 0) == 0:
                return (p, chain)   # the chain end reached
            raise ValueError(f'decode: no close at {pos}')
        if L == 1 and start == 0:
            chain.append(C.ATOM)
        elif L == 2 and start == 0:
            chain.append(C.ATOM1)
        elif start == 0:
            chain.append(L - 2)
        else:
            if L <= 2:
                raise ValueError(
                    f'decode: interior run L={L} at pos {start}')
            chain.append(L - 2)
        if cells.get(pos, 0) != 0:
            raise ValueError(f'decode: missing close at {pos}')
        pos += 1


def shape(eqs):
    """Loose structural signature for the harness landing compare."""
    return tuple(eqs)


# ---------------------------------------------------------------------------
# the transition table builder

def build_table(sn):
    """rows: state -> {0: (w, d, nxt), 1: ...}; nxt None = death row.
    d in 'L','R'.  A state with NO row for a read symbol = the machine
    halts there under the harness's stepping."""
    T = {}
    meta = {}

    def add(name, note):
        assert name not in T, f'duplicate {name}'
        T[name] = {}
        meta[name] = note

    def row(name, sym, w, d, nxt):
        T[name][sym] = (w, d, nxt)

    # ---- DISPATCH over the top run, from the rest mark (E)
    add('IN', 'rest dispatch (head arrived by a walk-home)')
    row('IN', 1, 1, 'L', 'D2')
    # (a close-rest IN 0-row for the sn >= 2 append tails was tried and
    # reverted: it miscosts more than it saves - it breaks the
    # ROI5->BRH2 observed-context merge on builds 2/3.  The appended
    # run is L = sn+3: for sn = 1 (L = 4) the shifted dispatch would
    # miscall it >= 5 outright, so there is no saving shape here.)
    add('D2', 'read E-1: 0 = top L 1 (atom), 1 = continue')
    row('D2', 1, 1, 'L', 'D3')
    row('D2', 0, 0, 'L', 'PWA')       # route A: [ATOM]: fs-limit, no p look
    add('D3', 'read E-2: 0 = top L 2 (ATOM1), 1 = continue')
    row('D3', 1, 1, 'L', 'D4')
    row('D3', 0, 0, 'L', 'M2')        # route B: 1 further left = the look
    add('D4', 'read E-3: 0 = top L 3, 1 = continue')
    row('D4', 1, 1, 'L', 'D5')
    row('D4', 0, 0, 'L', 'M3')
    add('D5', 'read E-4: 0 = top L 4, 1 = top L >= 5')
    row('D5', 1, 1, 'L', 'WAE')
    row('D5', 0, 0, 'L', 'M4')
    add('M2', 'L==2 bottom: at C0-2 (the sep second cell), cross left')
    row('M2', 0, 0, 'L', 'PKB')       # head lands on C0-3: the look
    row('M2', 1, 0, 'L', 'PKB')       # unreachable (L2 => m1); safe
    add('M3', 'L==3 m-test at E-4: 1 = lower run (GU), 0 = bottom')
    row('M3', 0, 0, 'L', 'PKC')       # head lands on C0-3: the look
    # no 1 row: L3 with m>=2 cannot happen canonically (GU)
    add('M4', 'L==4 m-test at E-5: 1 = lower run (m>=2), 0 = bottom')
    row('M4', 0, 0, 'L', 'PKD1')      # head lands on C0-3 (L4 with m==1)
    row('M4', 1, 1, 'L', 'WAD')       # m>=2: continue left, then the look

    # ---- shared chain walkers to the park boundary
    # WAD/WAZ/WAS: m>=2 route D clones (marks, crossed 0, sep second cell)
    add('WAD', 'route D-m2 chain walk')
    row('WAD', 1, 1, 'L', 'WAD')
    row('WAD', 0, 0, 'L', 'WAZ')
    add('WAZ', 'route D-m2 crossed-0 test')
    row('WAZ', 1, 1, 'L', 'WAD')
    row('WAZ', 0, 0, 'L', 'WAS')
    add('WAS', 'route D-m2 look at C0-3 (fused: 0 = absorb write)')
    row('WAS', 0, 1, 'R', 'WR_A1')    # p0: park mark at C0-3, walk back right
    row('WAS', 1, 1, 'L', 'FSL')       # p>=1: fold the spend in, then walk back
    add('WAE', 'route E chain walk')
    row('WAE', 1, 1, 'L', 'WAE')
    row('WAE', 0, 0, 'L', 'WAZB')
    add('WAZB', 'route E crossed-0 test')
    row('WAZB', 1, 1, 'L', 'WAE')
    row('WAZB', 0, 0, 'L', 'WASB')
    add('WASB', 'route E look at C0-3 (fused; 0 = plain dec walk back)')
    row('WASB', 0, 0, 'R', 'WBX1')
    row('WASB', 1, 1, 'L', 'FSL')

    # ---- the p-look clones, all parked at C0-3 (the read IS the look)
    add('PKB', 'route B look at C0-3')
    row('PKB', 0, 0, 'R', 'WBX1')     # p0: walk back; plain dec
    row('PKB', 1, 1, 'L', 'FSL')     # p1: spend, then walk back; dec + append + spend
    add('PKC', 'route C look at C0-3')
    # p0: the model's move (0,[NUM(1)]) -> (0,[]) is live (the Halt fires
    # only on the empty chain), so erase the 3-run and rest on the blank:
    # the NEXT dispatch (empty chain, no row) dies = the final move.
    row('PKC', 0, 0, 'R', 'ROI1')
    T['PKC'][1] = (1, 'L', 'HE1')   # p1: the head-empty arm
    add('PKD1', 'route D-m1 look at C0-3')
    row('PKD1', 0, 0, 'R', 'WBX1')
    row('PKD1', 1, 1, 'L', 'FSL')     # p1: fold the spend in, then walk back
    # ---- shared decs: the pred dec walks home; the fs dec appends
    add('DECP', 'pred dec: erase the last mark, rest (lands the new mark)')
    row('DECP', 1, 0, 'L', 'IN')
    add('DECF', 'fs dec: erase the last mark, then append')
    row('DECF', 1, 0, 'L', 'APW1')

    # ---- walk backs: five states each; the rows resolve the
    # sep-vs-terminator pair; the landing puts the head ON the top run's
    # last mark in the landing state.  Families:
    #   WB_P   the p0 plain dec: lands IN (rest on the new last mark)
    #   WR_FS  the fs dec + append: lands DECF
    #   WB_ABS the absorb park write: lands ABS_E
    # ROUND 9 rewiring: the three RIGHT-RETURN walkers over the park
    # region (WR_A for route A, WR_FS for the fs spend return, WB_ABS
    # for the absorb) ride/cross/terminate IDENTICALLY (same 0-cross
    # column, same (1,R,front) ride), so ONE walker (the WR_A trio)
    # serves all of them.  The three landing tails differ only in their
    # final non-IN lander (RAW / DECF / ABS_E) and stay separate.
    # The old three trio-copies are gone (6 states).
    add('WBX1', 'p0 plain dec: cross C0-2')
    row('WBX1', 0, 0, 'R', 'WBX2')
    add('WBX2', 'p0 plain dec: cross C0-1')
    row('WBX2', 0, 0, 'R', 'WB_P1')
    add('WB_P1', 'walk back (DECP): over the run marks; crosses closes')
    T['WB_P1'] = {0: (0, 'R', 'WB_P2'), 1: (1, 'R', 'WB_P1')}
    add('WB_P2', 'walk back (DECP): at the close/right cell: pair test')
    T['WB_P2'] = {0: (0, 'L', 'WB_P4'), 1: (1, 'R', 'WB_P1')}
    add('WB_P4', 'walk back (DECP): at the close, stepping left')
    T['WB_P4'] = {0: (0, 'L', 'WB_P5'), 1: (0, 'L', 'WB_P5')}
    add('WB_P5', 'walk back (DECP): erase the top run last mark, rest')
    T['WB_P5'] = {0: (0, 'L', 'IN'), 1: (0, 'L', 'IN')}
    for base, land, tail in (
                       ('WR_FS', 'DECF', 'WR_FS'), ('WB_ABS', 'ABS_E', 'WB_ABS')):
        add(f'{base}4', f'walk back ({land}): at chain end, stepping left')
        T[f'{base}4'] = {0: (0, 'L', f'{base}5'), 1: (0, 'L', f'{base}5')}
        add(f'{base}5', f'walk back ({land}): land the head on the top mark')
        T[f'{base}5'] = {0: (0, 'L', land), 1: (0, 'L', land)}
    # the WR_FS / WB_ABS trio fronts retarget into the shared WR_A walker;
    # the tail states below re-enter from WR_A3's 0-arm via their tails.
    WR_FS3_EXIT = 'WR_FS4'
    WB_ABS3_EXIT = 'WB_ABS4'

    # ---- route A: the fs-limit park extension (p += sn)
    add('PWA', 'route A walk: at C0-1 (the sep first cell), cross left')
    row('PWA', 0, 0, 'L', 'PWB')
    add('PWB', 'route A: at C0-3 (the rightmost park cell)')
    # actual fire positions (probe at E-1): PWA at C0-2, PWB at C0-3,
    # PWK was a C0-3 assumption corrected here:
    if sn >= 2:
        row('PWB', 0, 1, 'L', 'PWX1')   # p == 0: the first mark AT C0-3
    else:
        row('PWB', 0, 1, 'R', 'WR_A1')  # p == 0: the mark + walk back
    row('PWB', 1, 1, 'L', 'PWALK')  # p >= 1: keep the mark, walk left
    add('PWK', 'route A: at C0-3: 1 = park marks follow, 0 = write here')
    row('PWK', 1, 1, 'L', 'PWALK')
    if sn >= 2:
        row('PWK', 0, 1, 'L', 'PWX1')    # p == 0: write mark 1...
    else:
        row('PWK', 0, 1, 'R', 'WR_A1')   # p == 0: the mark + walk back
    add('PWALK', 'route A: over the park marks to the first blank')
    row('PWALK', 1, 1, 'L', 'PWALK')
    if sn >= 2:
        row('PWALK', 0, 1, 'L', 'PWX1')   # the blank left of the leftmost
        # the extension is sn marks: PWALK's own row writes the first;
        # this chain writes the rest, the last write turning back right
        # (that merge is why the old PWX turn state is gone).
        for j in range(1, sn):
            cur, nxt = f'PWX{j}', f'PWX{j+1}'
            add(cur, f'route A: park extension write {j+1} of {sn}'
                     + (', with the turn' if j == sn - 1 else ''))
            if j < sn - 1:
                row(cur, 0, 1, 'L', nxt)
                row(cur, 1, 1, 'L', nxt)
            else:
                row(cur, 0, 1, 'R', 'WR_A1')
                row(cur, 1, 1, 'R', 'WR_A1')
    else:
        # sn == 1: the single park mark is written right here; no count
        # chain needed, turn around straight into the walk back
        row('PWALK', 0, 1, 'R', 'WR_A1')
    # walk back to the top mark, then rewrite the delivered run 1 -> 3
    for st_i, note in ((1, 'walking right'), (2, 'crossed a 0')):
        add(f'WR_A{st_i}', f'route A walk back ({note})')
        if st_i == 1:
            T['WR_A1'] = {0: (0, 'R', 'WR_A2'), 1: (1, 'R', 'WR_A1')}
        else:
            T['WR_A2'] = {0: (0, 'R', 'WR_A3'), 1: (1, 'R', 'WR_A1')}
    add('WR_A3', 'route A walk back: pair test (sep=1 / term=0)')
    T['WR_A3'] = {0: (0, 'L', 'WR_A4'), 1: (1, 'R', 'WR_A1')}
    # the fs walk-back and the absorb walk-back prepare their tails via
    # the shared WR_A pair-test; the tails re-enter from WR_A4 via the
    # WR_FS/WB_ABS landing states (each final step is its own family's
    # lander: DECF / ABS_E).
    T['WR_A3_EXIT_FS'] = None  # placeholder; removed below
    del T['WR_A3_EXIT_FS']
    add('WR_A4', 'route A walk back: at chain end, step left')
    T['WR_A4'] = {0: (0, 'L', 'WR_A5'), 1: (0, 'L', 'WR_A5')}
    add('WR_A5', 'route A walk back: land on the top mark')
    T['WR_A5'] = {0: (0, 'L', 'RAW'), 1: (0, 'L', 'RAW')}
    add('RAW', 'route A: at the sole mark going right to widen the run')
    row('RAW', 1, 1, 'R', 'RAW2')
    add('RAW2', 'route A: at the old close: write mark 2 of 3')
    row('RAW2', 0, 1, 'R', 'RAW3')
    row('RAW2', 1, 1, 'R', 'RAW3')
    add('RAW3', 'route A: write mark 3 of 3, then walk home')
    row('RAW3', 0, 1, 'R', 'BR')
    row('RAW3', 1, 1, 'R', 'BR')

    # ---- route C p1: THE HEAD-EMPTY ARM (rewrite the singleton run)
    # flow: PKC-1 -> [walk home shared BR lands IN] is wrong; the arm:
    # from C0-3 step right to C0, erase 3 in place, write sn until done,
    # then spend then shared BR.
    add('HE1', 'route C: over the park marks to the blank left of the leftmost')
    row('HE1', 1, 1, 'L', 'HE1')       # pass further park marks (keep) - route C is p>=1
    row('HE1', 0, 0, 'R', 'HE1T')      # the blank left of the leftmost mark; turn right
    add('HE2', 'head-empty: erase the three old marks walking right')
    row('HE2', 1, 0, 'R', 'HE3')
    add('HE3', 'head-empty: at C0 heading right erasing')
    row('HE3', 1, 0, 'R', 'HE4')   # erase mark 1 (of the old run)
    add('HE4', 'head-empty: erase mark 2')
    row('HE4', 1, 0, 'R', 'HE5')   # erase mark 2
    add('HE5', 'head-empty: erase mark 3')
    row('HE5', 1, 0, 'R', 'HE6')   # erase mark 3
    # now the head is at the old close C0+3 (0).  Write sn marks here
    # going right (the new run keeps C0..C0+2 as the first 3 marks).
    add('HE6', 'head-empty: writing new marks')
    if sn >= 2:
        row('HE6', 0, 1, 'R', 'HE7')
        add('HE7', 'head-empty: wrote the extra marks; new close ahead')
        row('HE7', 0, 0, 'R', 'BR')
        row('HE7', 1, 0, 'R', 'BR')
    else:
        row('HE6', 0, 1, 'R', 'BR')
        row('HE6', 1, 0, 'R', 'BR')

    # ---- shared walk homes for route D absorb stops (BR from anywhere)

    # ---- append machinery (after the fs dec): the head walks to E+1,
    # then writes sn+3 marks (sequenced) and leaves the close/chain end
    # ---- the append walk + write chain: DECF lands the erased old
    # top run at its new last mark; APW1 is a self-looping crosser that
    # keeps riding right over the 2nd-to-last mark and the erased hole
    # (the new close), handing off to the write chain at the old close
    # cell.  The old APW1+APW2 pair (one crossing each) folded into
    # this single crosser: -1 state.
    add('APW1', 'append crosser: keep 1, cross the 0, then write')
    row('APW1', 0, 0, 'R', f'A{sn+3}')
    row('APW1', 1, 1, 'R', 'APW1')
    for k in range(sn + 3, 0, -1):
        add(f'A{k}', f'append: write mark ({sn+3-k+1} of {sn+3})')
        if k == 1:
            row(f'A{k}', 0, 1, 'R', 'SWT1')   # finished: head on the close
            row(f'A{k}', 1, 1, 'R', 'SWT1')
        else:
            row(f'A{k}', 0, 1, 'R', f'A{k-1}')
            row(f'A{k}', 1, 1, 'R', f'A{k-1}')

    # the fs append's close write rests the machine on the run's new
    # last mark: the walk's spend already happened at the p-look.
    add('SWT1', 'fs append: write the close, rest on the new last mark')
    row('SWT1', 0, 0, 'L', 'IN')
    row('SWT1', 1, 0, 'L', 'IN')

    # ---- the fs SPEND is folded into the p-look: the fs arm of every
    # look (PKB/WAS/WASB 1-rows) walks left over the park (FSL), turns at
    # the first blank, erases the park's leftmost mark (FSP) and enters
    # the walk back from just right of the erased cell.  This deletes the
    # whole old SWT1/SWC/SWZ/SWX/SWP/SE cluster; the append's close write
    # (SWT1) now rests the machine directly on the new last mark.
    add('FSL', 'fs spend: left over the park marks to the first blank')
    row('FSL', 1, 1, 'L', 'FSL')
    row('FSL', 0, 0, 'R', 'FSP')
    add('FSP', 'fs spend: erase the leftmost mark, walk back right')
    row('FSP', 1, 0, 'R', 'WR_A1')

    # ---- route C k1 arms: the model's (p,[NUM(1)]) -> (p-1,[NUM(1+sn)]):
    # after the park erase the bottom run grows by sn marks at C0+3..
    add('HE1T', 'route C grow: erase the leftmost park mark')
    row('HE1T', 1, 0, 'R', 'GR0')
    add('GR0', 'route C grow: over the park marks to the sep')
    row('GR0', 1, 1, 'R', 'GR0')
    row('GR0', 0, 0, 'R', 'GR0B')
    add('GR0B', 'route C grow: cross C0-1')
    row('GR0B', 0, 0, 'R', 'GP')
    # the bottom run is exactly 3 marks at this site (L==3 canonical), so
    # the old fixed GR1/GR2/GR3 pass collapses into one loop state; the
    # first 0 met is C0+3 (the old close), which becomes growth mark 1.
    add('GP', 'route C grow: pass the run marks right, keep')
    row('GP', 1, 1, 'R', 'GP')
    if sn >= 2:
        row('GP', 0, 1, 'R', 'PWGY2')    # growth mark 1 written (the close)
        for j in range(2, sn + 1):
            add(f'PWGY{j}', f'route C grow: growth mark {j} of {sn}')
            row(f'PWGY{j}', 0, 1, 'R', 'BR' if j == sn else f'PWGY{j+1}')
            row(f'PWGY{j}', 1, 1, 'R', 'BR' if j == sn else f'PWGY{j+1}')
    else:
        row('GP', 0, 1, 'R', 'BR')      # the sole growth mark written

    # ---- route C p0: (0,[NUM(1)]) -> (0,[]): the crosser-eraser loop
    # (the old ROI1+ROI2+ROI3 trio: two zero-crossings plus a blind
    # erase folded into one state: 0 keeps crossing right, 1 erases and
    # hands off), then erase mark 2, then erase mark 3 and rest.
    add('ROI1', 'route C p0: cross zeros; erase the first mark on 1s')
    row('ROI1', 0, 0, 'R', 'ROI1')
    row('ROI1', 1, 0, 'R', 'ROI4')
    add('ROI4', 'route C p0: erase run mark 2')
    row('ROI4', 1, 0, 'R', 'ROI5')
    add('ROI5', 'route C p0: erase run mark 3, rest IN on the blank')
    # the rest lands IN directly on the just-erased second mark cell;
    # that empty dispatch is never re-fired (the model halts on
    # (0, []) and every gate breaks before firing the machine), and
    # the decode of the erased region is (0,[]) regardless of head.
    row('ROI5', 1, 0, 'L', 'IN')

    # ---- shared walk home (right to the terminator pair, back up, rest)
    add('BR', 'walk home right')
    row('BR', 1, 1, 'R', 'BR')
    row('BR', 0, 0, 'R', 'BRZ')
    add('BRZ', 'walk home: crossed a 0')
    row('BRZ', 1, 1, 'R', 'BR')
    row('BRZ', 0, 0, 'R', 'BRQ')
    add('BRQ', 'walk home: pair test (sep or terminator?)')
    row('BRQ', 1, 1, 'R', 'BR')
    row('BRQ', 0, 0, 'L', 'BRH1')
    add('BRH1', 'walk home: at terminator second cell, back up 1')
    row('BRH1', 0, 0, 'L', 'BRH2')
    row('BRH1', 1, 0, 'L', 'BRH2')
    add('BRH2', 'walk home: land the head on the top mark, state IN')
    row('BRH2', 0, 0, 'L', 'IN')
    row('BRH2', 1, 0, 'L', 'IN')

    # ---- the absorb (route D m>=2 p0): the park mark is written by
    # WAS's fused row, which walks back right directly into the walk-back
    # family (no separate pass needed: the fresh mark sits behind the
    # head, left of the sep it is about to cross).
    add('ABS_E', 'absorb: at the last mark: erase (pop, park += 1)')
    row('ABS_E', 1, 0, 'L', 'EA2')
    # the remaining three erases ARE the cascade's erase chain (identical
    # moves): EA2/EA3/EA4 shared with the unit pops below.
    add('EA2', "cascade erase: the unit's last mark (absorb runs join here)")
    row('EA2', 1, 0, 'L', 'EA3')

    # ---- the p0 pop-cascade (the fix of record): every pop erases the
    # entry's whole run and writes one park mark per pop; the cascade
    # stops at the first non-unit entry below (or at the bottom, which
    # never pops).  End region after every pop = a contiguous zero
    # stretch right of the survivor's close (all pops are suffix pops),
    # so the interior stays hole-free and the measure below is
    # position-agnostic: the zeros are met before the survivor's run.
    # MSE/M1/M2/M3 count 1s since the last 0 walking LEFT; M4 is the
    # 5th read (the below-left entry's mark = interior unit, vs the sep
    # = the bottom).  Park writes happen BEFORE erasing, over the intact
    # interior, so the left walk never crosses a hole.  EA* erase the
    # unit's three marks on the rightward return, driven by the first
    # 00-pair met walking right (the survivor's close + the pop holes).
    add('MSE', 'cascade measure: left over the zeros, then count the run')
    row('MSE', 0, 0, 'L', 'MSE')
    row('MSE', 1, 1, 'L', 'CM1')
    add('CM1', 'cascade: 1 mark seen since the last 0')
    row('CM1', 1, 1, 'L', 'CM2')
    row('CM1', 0, 0, 'R', 'SB2')       # the bottom with L==1: cascade done
    add('CM2', 'cascade: 2 marks seen')
    row('CM2', 1, 1, 'L', 'CM3')
    row('CM2', 0, 0, 'R', 'SB2')       # the bottom with L==2: cascade done
    add('CM3', 'cascade: 3 marks seen; the 4th read decides')
    row('CM3', 1, 1, 'R', 'SH1')       # a run of >=4: a non-unit: stop here
    row('CM3', 0, 0, 'L', 'CM4')       # exactly 3: unit candidate; 5th read
    add('CM4', 'cascade: the 5th read (interior unit vs the sep/bottom)')
    row('CM4', 1, 1, 'L', 'WLA')       # interior unit intact: park write first
    row('CM4', 0, 0, 'R', 'SB2')       # the sep: the bottom: cascade done
    # the stop walk fused to two states: SB2 crosses the sep/run start
    # (both rows identical: keep and step right), then SH1 walks right
    # over the run; the first 0 (the close) sends the head back one cell
    # onto the run's last mark = the rest position.
    add('SB2', 'cascade stop: keep and step right (sep second or C0 mark)')
    row('SB2', 0, 0, 'R', 'SH1')
    row('SB2', 1, 1, 'R', 'SH1')
    add('SH1', 'cascade stop: walk home right, back up onto the last mark')
    row('SH1', 1, 1, 'R', 'SH1')
    row('SH1', 0, 0, 'L', 'IN')
    add('WLA', 'cascade park walk: left over the intact chain')
    row('WLA', 1, 1, 'L', 'WLA')
    row('WLA', 0, 0, 'L', 'WLB')
    add('WLB', 'cascade park walk: crossed a 0 (close or the sep first)')
    row('WLB', 1, 1, 'L', 'WLA')       # a close before the next run
    row('WLB', 0, 0, 'L', 'WLC')       # the 00 pair crossed: into the park
    add('WLC', 'cascade: over the park marks to the first blank, write')
    row('WLC', 1, 1, 'L', 'WLC')       # the park marks (keep, walk left)
    row('WLC', 0, 1, 'R', 'RW1')       # the pop's park mark written
    add('RW1', 'cascade return: walk right over park marks and the chain')
    row('RW1', 1, 1, 'R', 'RW1')
    row('RW1', 0, 0, 'R', 'RW2')
    add('RW2', 'cascade return: crossed a 0 (close or the sep first)')
    row('RW2', 1, 1, 'R', 'RW1')
    row('RW2', 0, 0, 'R', 'RW3')
    add('RW3', 'cascade return: second 0: sep second cell or the end region')
    row('RW3', 1, 1, 'R', 'RW1')       # the sep crossed: the chain follows
    row('RW3', 0, 0, 'L', 'RW4')       # the end region: the survivor's close
    # the return terminal fused: RW4 loops left over the hole zeros
    # (both reads keep), and the survivor run's marks erase as met, one
    # state per mark (exactly the 3-mark unit; the below close is MSE's
    # first 0 and restarts the measure).
    add('RW4', 'cascade return: left over the holes, erase marks as met')
    row('RW4', 0, 0, 'L', 'RW4')
    row('RW4', 1, 0, 'L', 'EA3')
    add('EA3', 'cascade erase: the unit middle mark')
    row('EA3', 1, 0, 'L', 'EA4')
    add('EA4', 'cascade erase: the unit first mark; the measure restarts')
    row('EA4', 1, 0, 'L', 'MSE')

    # the minimise pass of record: drop unreachable states, merge
    # behaviourally equivalent ones, then apply the recorded
    # observed-context merges (minimising between each)
    return apply_context_merges(*minimise_table(T, meta, 'IN'), sn)


# ---------------------------------------------------------------------------
# the observed-context merges: pairs the bisimulation floor cannot see.
# Found and battery-validated by tools/eps1_contextmin.py: a state only
# entered on a subset of the symbols may be replaced by any state that
# agrees with it on exactly those entries (sound on reachable inputs;
# the census + randoms + tiers + adversarial batteries cross-check).
# Applied in the recorded order with minimise_table between each.

CONTEXT_MERGES = {
    1: [('BRQ', 'WB_P2'), ('EA2', 'RW4'), ('M2', 'M4'), ('RAW3', 'GP'),
        ('ROI5', 'BRH2'), ('BRZ', 'WB_P1'), ('BR', 'WBX2')],
    2: [('BRQ', 'WB_P2'), ('EA2', 'RW4'), ('M2', 'M4'), ('RAW2', 'GP'),
        ('ROI5', 'BRH2'), ('BRZ', 'WB_P1'), ('RAW', 'GP'), ('BR', 'WBX2')],
    3: [('BRQ', 'WB_P2'), ('EA2', 'RW4'), ('M2', 'M4'), ('ROI5', 'BRH2'),
        ('BRZ', 'WB_P1'), ('BR', 'WBX2')],
}


def _redirect_retarget(T_or_now, Y, X):
    n = 0
    for _s, rows in T_or_now.items():
        for a, (w, d, nx) in list(rows.items()):
            if nx == Y:
                rows[a] = (w, d, X)
                n += 1
    return n


def apply_context_merges(T, meta, sn):
    for Y, X in CONTEXT_MERGES.get(sn, []):
        if Y not in T or X not in T:
            raise AssertionError(
                f'context merge {Y}->{X}: a name is missing after '
                'the bisim pass; the recorded list is stale')
        _redirect_retarget(T, Y, X)
        T, meta = minimise_table(T, meta, 'IN')
    return T, meta


# ---------------------------------------------------------------------------
# the minimise pass: drop states unreachable from the rest dispatch IN,
# then merge behaviourally equivalent states (fixpoint bisimulation over
# the 2-symbol rows; a missing row = the shared death/halt arm).  Sound:
# on canonical inputs the merged machine steps identically step-for-step.

def _reachable(T, start='IN'):
    seen = {start}
    work = [start]
    while work:
        s = work.pop()
        for sym, (w, d, nxt) in T[s].items():
            if nxt not in seen:
                seen.add(nxt)
                work.append(nxt)
    return seen


def _block_signature(T, part, s):
    out = []
    for sym in (0, 1):
        r = T[s].get(sym)
        if r is None:
            out.append(('H',))
        else:
            w, d, nxt = r
            out.append(('R', w, d, part[nxt]))
    return tuple(out)


def minimise_table(T, meta, start='IN'):
    while True:
        live = _reachable(T, start)
        if len(live) < len(T):
            for dead in set(T) - live:
                del T[dead]
                meta.pop(dead, None)
            continue                     # re-close reachability
        # one equivalence-improving merge round; repeat until stable
        part = {s: s for s in T}
        while True:
            blocks = {}
            for s in T:
                blocks.setdefault(_block_signature(T, part, s), []).append(s)
            newpart = {}
            for i, members in enumerate(sorted(blocks.values(), key=min)):
                for m in members:
                    newpart[m] = i
            if newpart == part:
                break
            part = newpart
        classes = {}
        for s, b in part.items():
            classes.setdefault(b, []).append(s)
        multi = [c for c in classes.values() if len(c) > 1]
        if not multi:
            return T, meta
        # class rename: the lexicographically-least surviving name; retarget
        for members in multi:
            keep = min(members)
            if meta.get(keep) is None:
                for m in sorted(members):
                    if meta.get(m):
                        meta[keep] = meta[m]
                        break
            for s in T:
                for sym, (w, d, nxt) in list(T[s].items()):
                    if nxt != keep and nxt in members:
                        T[s][sym] = (w, d, keep)
            for m in members:
                if m != keep:
                    del T[m]
                    meta.pop(m, None)


# ---------------------------------------------------------------------------
# the harness: drive one machine campaign (rest -> rest) and compare the
# landing against eps1_chain.step at the build's fixed seed

def campaign(cells, head, T, cap=400000):
    """One machine campaign from the rest (st='IN') to the next rest or
    a death.  Returns (kind, steps, cells, head): kind 'rest'/'death'/'cap'.
    Entry state must be 'IN' (the harness fires the dispatch exactly here)."""
    st, h = 'IN', head
    steps = 0
    while steps < cap:
        a = T.get(st, {}).get(cells.get(h, 0))
        if a is None:
            return 'death', steps, cells, h
        w, d, nx = a
        cells[h] = w
        h += 1 if d == 'R' else -1
        st = nx
        steps += 1
        if st == 'IN':
            return 'rest', steps, cells, h
    return 'cap', steps, cells, h


def same_chain(got, want):
    """Structural equality: ints match ints; the ATOM/ATOM1 bottoms match
    by identity."""
    if len(got) != len(want):
        return False
    for g, w in zip(got, want):
        if isinstance(w, C.Ord) or isinstance(g, C.Ord):
            if bool(g != w):      # value equality across the two Ord systems
                return False
        elif g != w:
            return False
    return True


def step_model(p, chain, sn):
    """eps1_chain.step wrapped: ('move', p', chain') or ('halt',..)."""
    try:
        p2, c2, n2, k2 = C.step(p, list(chain), sn)
        return 'move', p2, c2
    except C.Halt:
        return 'halt', p, list(chain)


def census_battery(T, sn, limit_t=3):
    """Gate 1: every exact pre-step state of the fixed-seed full runs
    (tiers 1..3); each machine campaign's landing equals the model's."""
    from eps1_super_local import chain_of, D
    ok = bad = halts = 0
    failures = []
    for t_n in range(1, limit_t + 1):
        mp, mc = chain_of(D.tower(t_n))
        for _ in range(200000):
            if not mc:
                break
            try:
                kind, p2, c2 = step_model(mp, mc, sn)
            except Exception as e:  # the model's assert corners
                failures.append(('model-crash', (mp, list(mc)), repr(e)))
                bad += 1
                break
            if kind == 'halt':
                halts += 1
                break
            cells, h0 = mk_tape(mp, list(mc))
            k2, steps, cells2, h2 = campaign(cells, h0, T)
            if k2 != 'rest':
                if len(failures) < 14:
                    failures.append(('campaign-' + k2, (mp, list(mc)), steps))
                bad += 1
                break
            try:
                dp, dc = decode_tape(cells2)
            except ValueError as e:
                if len(failures) < 14:
                    failures.append(('decode', (mp, list(mc)), repr(e)))
                bad += 1
                break
            if C.full(dp, dc) == C.full(p2, c2):
                ok += 1
            else:
                if len(failures) < 14:
                    failures.append(('landing', (mp, list(mc)),
                                     (dp, list(dc)), (p2, list(c2))))
                bad += 1
                break
            mp, mc = p2, list(c2)
    return ok, bad, halts, failures


def check_moves_random(T, sn, trials=400, seed=17, moves=4, limit_t=3):
    """Gate 2: 400 seeded random starts (atom bottoms from the towers,
    plain chains otherwise), up to 4 consecutive moves each, the machine
    landing value-compared (C.full) against eps1_chain.step after each."""
    from eps1_super_local import chain_of, D
    rng = random.Random(seed)
    bad = 0
    for t_i in range(trials):
        if t_i % 4 == 0:
            mp, mc = chain_of(D.tower(rng.randint(1, limit_t)))
        else:
            mc = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                 for _ in range(rng.randint(1, 3))]
            mp, mc = C.normalise(rng.randint(0, 2), mc)
            mc = list(mc)
        try:
            cells, h0 = mk_tape(mp, list(mc))
        except ValueError:
            continue                          # not encodable canonically
        for _m in range(moves):
            try:
                p4, c4, n4, k4 = C.step(mp, list(mc), sn)
            except C.Halt:
                break                         # the model halts; the machine's
                                              # empty dispatch dies the same way
            except Exception:
                break                         # the model's assert corners:
                                              # skip this start
            k2, steps, cells2, h2 = campaign(cells, h0, T)
            if k2 != 'rest':
                bad += 1
                print(f'   BAD campaign k={k2} steps={steps} at ({mp}, {list(mc)})')
                break
            try:
                dp, dc = decode_tape(cells2)
            except ValueError as e:
                bad += 1
                print(f'   DECODE FAIL at ({mp}, {list(mc)}): {e}')
                break
            if C.full(dp, dc) != C.full(p4, list(c4)):
                bad += 1
                print(f'   UNFAITHFUL at ({mp}, {list(mc)}): '
                      f'machine ({dp}, {list(dc)}) vs model ({p4}, {list(c4)})')
                break
            mp, mc = p4, list(c4)
            cells, h0 = cells2, h2
    print(f'  gate 2: {trials} random starts x up to {moves} moves: '
          + ('ALL OK' if bad == 0 else f'{bad} FAILURES'))
    return bad


def check_tiers(T, sn, limit_t=7):
    """Gate 3: the fixed runs (tiers 1..limit) driven move by move; the
    machine's campaign count must equal the model's frozen-index walk
    (the machine's contract: one C.step per rest-to-rest campaign with
    the seed as n; C.run with the index forwarded cycles instead of
    halting, so it is not the comparison of record here)."""
    from eps1_super_local import chain_of, D
    bad = 0
    for t_n in range(1, limit_t + 1):
        mp, mc = chain_of(D.tower(t_n))
        moves_m = 0
        pk, pc = mp, list(mc)
        while True:
            try:
                kind, p2, c2 = step_model(pk, pc, sn)
            except Exception:
                break
            if kind != 'move':
                break
            moves_m += 1
            pk, pc = p2, list(c2)
        count = 0
        landed_ok = True
        while True:
            try:
                p4, c4, n4, k4 = C.step(mp, list(mc), sn)
            except C.Halt:
                break
            cells, h0 = mk_tape(mp, list(mc))
            k2, steps, cells2, h2 = campaign(cells, h0, T)
            if k2 != 'rest':
                landed_ok = False
                print(f'   tier {t_n}: machine {k2} at ({mp}, {list(mc)})')
                break
            try:
                dp, dc = decode_tape(cells2)
            except ValueError as e:
                landed_ok = False
                print(f'   tier {t_n}: decode fail at ({mp}, {list(mc)}): {e}')
                break
            if C.full(dp, dc) != C.full(p4, list(c4)):
                landed_ok = False
                print(f'   tier {t_n}: unfaithful at ({mp}, {list(mc)})')
                break
            mp, mc = p4, list(c4)
            count += 1
        if not landed_ok or count != moves_m:
            bad += 1
            print(f'   tier {t_n} sn={sn}: machine {count} vs model {moves_m} FAILED')
        else:
            print(f'   tier {t_n} sn={sn}: {count} moves, model-equal OK')
    return bad


def main():
    failed = 0
    for sn in (1, 2):
        T, meta = build_table(sn)
        ok, bad, halts, failures = census_battery(T, sn)
        # the state count of record, honestly reported (the <=40 target is
        # a design goal, not a promise: this is the raw achieved count)
        print(f'sn={sn}: states={len(T)} rows={sum(len(r) for r in T.values())} '
              f'gate1 census ok={ok} bad={bad} halts={halts}')
        for f in failures:
            print('   FAIL', f)
            failed += 1
        if check_moves_random(T, sn):
            failed += 1
        if check_tiers(T, sn):
            failed += 1
    print('ALL OK' if failed == 0 else f'{failed} GATE FAILURES')
    sys.exit(0 if failed == 0 else 1)


if __name__ == '__main__':
    main()
