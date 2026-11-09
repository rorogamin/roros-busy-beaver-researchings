"""The eps_1 chain machine as a 2-symbol table: geometry, decoder, the copy.

`tools/eps1_chain.py` fixes the moves at the level of (p, chain, n).  This module
is the same machine on tape.  It is built in the order the plan lists: the
geometry and its decoder, then the index copy (the only genuinely hard routine),
then the dispatch, the moves and the build.

## Tape

    [free] 1^p (park)  0 0  1^{c0} 0 1^{c1} 0 ... 0 1^{cm}  0 0  1^n (index)  [free]
            Lp..Rp           C0                                X..

  * the park is the wrap count p, a unary block whose *right* end Rp is fixed
    forever, so "is there a park" is a fixed look three cells left of C0;
  * the chain is the active chain, bottom-first, entries as runs separated by a
    single blank; entry code: run length 1 = eps_0, 2 = eps_0+1, L >= 3 = the
    number L-2;
  * the index is the Hardy index n, a unary block;
  * free space is two or more blanks.  A single blank is a chain separator.

Routines are entered and left at a *home*, a position the model can be read from:

    HT   on the chain's top run's last mark E (the acting entry)

The two invariants the moves keep, and the reason the geometry works:

    I1  Rp = C0-3, so the park's right end never moves and p = 0 is a look at
        C0-3.  Spending erases the park's *leftmost* mark and growing writes one
        cell left of it, so both leave the right end alone.
    I2  X = E+3 while the index is at its resting distance: two blanks between
        the chain's top run and the index.  pred moves E and X left by one
        together, so it costs nothing.  An fs write moves X right, and that is
        the copy.

`frame` lays a model state out on tape and `decode` reads a home back.  The copy
is checked on its own against `want_copy` before anything is spliced onto it.
"""

import sys

sys.path.insert(0, 'tools')
import tm
import eps1_chain as C
from eps1_chain import Ord, NUM, ATOM, ATOM1

# ---------------------------------------------------------------- the table
SNAME = {}
SID = {}
TBL = {}


def S(name):
    if name not in SID:
        SID[name] = len(SID)
        SNAME[SID[name]] = name
    return SID[name]


def row(st, sym, w, d, nxt):
    k = (S(st), sym)
    assert k not in TBL, f'duplicate row {st},{sym}'
    TBL[k] = (w, d, None if nxt is None else S(nxt))


def machine():
    return tm.TM(len(SID), dict(TBL))


# ---------------------------------------------------------------- layout
def code(entry):
    """Entry -> run length."""
    if isinstance(entry, Ord):
        if entry.is_atom():
            return 1
        if entry == ATOM1:
            return 2
        return entry.terms[0][1] + 2
    return entry + 2


def entry_of(L):
    if L == 1:
        return ATOM
    if L == 2:
        return ATOM1
    return NUM(L - 2)


def frame(p, chain, n):
    """Tape for (p, chain, n); head on HT.  Returns (tape, head, 'HT')."""
    tape = {}
    C0 = 4 + max(p, 1) + 3              # keep the chain's bottom clear of cell 0
    Rp = C0 - 3
    for i in range(p):
        tape[Rp - p + 1 + i] = 1
    pos = C0
    for k, e in enumerate(chain):
        if k:
            pos += 1
        L = code(e)
        for i in range(L):
            tape[pos + i] = 1
        pos += L
    E = pos - 1
    X = E + 3
    for i in range(n):
        tape[X + i] = 1
    return tape, E, home_of(p)


def decode(tape, head):
    """Tape -> (p, chain, n), with the head on HT (the top run's last mark)."""
    E = head
    if tape.get(E) != 1:
        raise ValueError(f'HT at {E} but no mark: {tm.tape_str(tape, E)}')
    runs = []
    q = E
    while True:
        ln = 0
        while tape.get(q - ln) == 1:
            ln += 1
        if ln == 0:
            raise ValueError('HT is not on a mark')
        runs.append(ln)
        low = q - ln + 1
        if tape.get(low - 1) == 1:
            raise ValueError('runs with no separator')
        if tape.get(low - 2) != 1:
            C0 = low
            break
        q = low - 2
    chain = [entry_of(L) for L in reversed(runs)]
    # the index: the first mark after two blanks right of E
    q = E + 1
    blank = 0
    while True:
        if tape.get(q) == 1:
            if blank >= 2:
                break
            blank = 0
        else:
            blank += 1
        q += 1
        if q - E > 10 ** 6:
            raise ValueError('no index found')
    X = q
    n = 0
    while tape.get(X + n) == 1:
        n += 1
    if tape.get(C0 - 3) == 1:
        q = C0 - 3
        while tape.get(q - 1) == 1:
            q -= 1
        p = C0 - 3 - q + 1
    else:
        p = 0
    return p, chain, n


def entry_key(e):
    """Value-key for a run entry: NUM(c) and the plain int c are the same run.

    ATOM and ATOM1 are not numbers and keep their identity; in particular
    ATOM1 (run length 2) must not collapse into NUM(1) (run length 3).
    """
    if isinstance(e, Ord):
        if e.is_atom() or e == ATOM1:
            return e
        return e.terms[0][1]
    return e


def same(a, b):
    """(p, chain, n) equality, with run entries compared by value."""
    if a[0] != b[0] or a[2] != b[2] or len(a[1]) != len(b[1]):
        return False
    for x, y in zip(a[1], b[1]):
        if entry_key(x) != entry_key(y):
            return False
    return True


# ---------------------------------------------------------------- the copy
#
# Entered at `CW0` with the head on E: the top run's last mark *after* the
# decrement.  The new run goes at E+1 and the index starts at E+3 with n marks.
#
#   after k trips:  1^{c} 0 [E+1..E+k] 0 [cursor E+k+2] 1^{n-k} 0 0 0 1^k
#
# One trip erases the cursor, writes the run's next mark two cells left of it,
# writes the index's next mark at the end of the copy (three reserved blanks past
# the source's right end) and comes back.  When the cursor is blank the source is
# drained: the run takes three more marks and the head lands on its last mark.

def copy_routine():
    row('CW0', 1, 1, 'R', 'CW1')            # E: the decremented run's last mark
    row('CW1', 0, 0, 'R', 'CW2')            # E+1: the separator
    row('CW2', 0, 1, 'R', 'CW3')            # E+2: the new run's first mark
    row('CW3', 0, 0, 'L', 'CWB')            # back onto it
    row('CWB', 1, 1, 'R', 'CBA')            # the run's last mark: one blank right
    row('CBA', 0, 0, 'R', 'CWC')            # the cursor, two right of it
    row('CWC', 1, 0, 'L', 'CWD')            # erase the cursor
    row('CWC', 0, 0, 'L', 'CF1')            # source drained: three marks and home
    row('CWD', 0, 1, 'R', 'CWE')            # write the run's mark, two left of it
    row('CWE', 0, 0, 'R', 'CX1')            # cross the erased cursor
    row('CX1', 1, 1, 'R', 'CX1')            # over the source's remaining marks
    row('CX1', 0, 0, 'R', 'CX2')            # first reserved blank
    row('CX2', 0, 0, 'R', 'CX3')            # second
    row('CX3', 0, 0, 'R', 'CX4')            # third: next is the copy's left end
    row('CX4', 1, 1, 'R', 'CX4')            # over the copy
    row('CX4', 0, 1, 'L', 'CY1')            # write the index's mark
    row('CY1', 1, 1, 'L', 'CY1')            # back over the copy
    row('CY1', 0, 0, 'L', 'CY2')            # third reserved blank
    row('CY2', 0, 0, 'L', 'CY3')            # second
    row('CY3', 0, 0, 'L', 'CY4')            # first: next is the source, or the cursor
    row('CY4', 1, 1, 'L', 'CY4')            # back over the source's remaining marks
    row('CY4', 0, 0, 'L', 'CWB')            # the cursor's blank, then the run's last mark
    row('CF1', 0, 1, 'R', 'CF2')            # finish: two marks, to n+3
    row('CF2', 0, 1, 'R', 'CF3')
    row('CF3', 0, 0, 'L', 'SP0')            # the head ends on the run's last mark; spend next


def dispatch_and_pred():
    """The two count walks, pred (shorten), and the halt.

    Homes H0 (p == 0) and H1 (p >= 1) are entered on E, the top run's last
    mark.  The count walks go left: A1/B1 see E-1, A2/B2 E-2, A3/B3 E-3, and
    A4 see E-4.  L = 1 is the fs-limit for both; L = 2 is pred on H0 and
    decrement+copy on H1; L = 3 is the halt on H0 and the head-empty arm on H1;
    L = 4 needs the bottom test on H0 only; L >= 5 is pred on H0 and
    decrement+copy on H1.
    """
    # --- H0: p == 0 ---------------------------------------------------------
    row('H0', 1, 1, 'L', 'A1')
    row('A1', 0, 0, 'L', 'AUX')            # singleton atom or a trailing unit
    row('A1', 1, 1, 'L', 'A2')
    row('A2', 0, 0, 'R', 'M1P')
    row('A2', 1, 1, 'L', 'A3')
    row('A3', 1, 1, 'L', 'A4')             # A3 on 0 has no row: the halt
    row('A4', 0, 0, 'L', 'A5')             # L = 4: bottom test at E-5
    row('A4', 1, 1, 'R', 'M3P')            # L >= 5: pred, head E-3
    row('A5', 0, 0, 'R', 'M4P')            # bottom: pred, head E-4
    row('A5', 1, 1, 'R', 'AB0')            # non-bottom: absorb, head E-4
    # --- H1: p >= 1 ---------------------------------------------------------
    row('H1', 1, 1, 'L', 'B1')
    row('B1', 0, 0, 'L', 'AUX')            # singleton atom or a trailing unit
    row('B1', 1, 1, 'L', 'B2')
    row('B2', 0, 0, 'R', 'M1F')
    row('B2', 1, 1, 'L', 'B3')
    row('B3', 0, 0, 'L', 'B3A')            # L = 3: a unit run or the bottom
    row('B3', 1, 1, 'L', 'B4')
    row('B3A', 1, 1, 'R', 'AB0T')          # a plain 1 above the bottom: normalise
    row('B3A', 0, 0, 'R', 'HE0')           # the bottom [NUM(1)]: head-empty
    row('B4', 0, 0, 'R', 'M3F')
    row('B4', 1, 1, 'R', 'M3F')
    # --- the walk back out to E (the bit is in the state) -------------------
    row('M1P', 1, 1, 'R', 'P0')
    row('M2P', 1, 1, 'R', 'M1P')
    row('M3P', 1, 1, 'R', 'M2P')
    row('M4P', 0, 0, 'R', 'M3P')
    row('M1F', 1, 1, 'R', 'F0')
    row('M2F', 1, 1, 'R', 'M1F')
    row('M3F', 1, 1, 'R', 'M2F')


def pred_shorten():
    """Erase E, extend the index left by one at E+2, home at E-1 on H0.

    Entered at P0 with the head on E.  E+1 is blank, E+2 is blank.
    """
    row('P0', 1, 0, 'R', 'P1')             # erase the acting mark
    row('P1', 0, 0, 'R', 'P2')             # E+1
    row('P2', 0, 1, 'L', 'P3')             # E+2: the index's new mark
    row('P3', 0, 0, 'L', 'P4')             # back over E+1
    row('P4', 0, 0, 'L', 'H0')             # over E onto E-1


def erase_for_copy():
    """The fs-successor's decrement: erase E and hand the copy E-1.

    The copy's CW0 is entered on E-1 and reads the decremented run's last mark.
    """
    row('F0', 1, 0, 'L', 'CW0')


def spend():
    """Erase the park's leftmost mark, then walk back to E' and home.

    Entry SP0: the head on E' (the top run's last mark), p >= 1.  The park is
    right-anchored at C0-3, so the walk left stops at C0-3 and then goes to the
    park's left end.  SPT reads the cell just right of the erased mark: a mark
    means the park survives (H1), a blank means it is empty (H0).
    """
    row('SP0', 1, 1, 'L', 'SP0')           # over the chain's runs
    row('SP0', 0, 0, 'L', 'SP1')           # onto the separator's left neighbour
    row('SP1', 1, 1, 'L', 'SP0')           # a single blank: an inside separator
    row('SP1', 0, 0, 'L', 'SP2')           # two blanks: onto C0-3
    row('SP2', 1, 1, 'L', 'SP2')           # over the park
    row('SP2', 0, 0, 'R', 'SPE')           # off its left end, back onto the mark
    row('SPE', 1, 0, 'R', 'SPT')           # erase the leftmost
    row('SPT', 1, 1, 'R', 'SW1')           # the park survives
    row('SPT', 0, 0, 'R', 'SW0')           # the park is empty
    # flag 1: over the rest of the park, the two-blank gap, the chain
    row('SW1', 1, 1, 'R', 'SW1')
    row('SW1', 0, 0, 'R', 'SG1')
    row('SG1', 0, 0, 'R', 'W11')
    row('W11', 1, 1, 'R', 'W11')
    row('W11', 0, 0, 'R', 'W21')
    row('W21', 1, 1, 'R', 'W11')
    row('W21', 0, 0, 'L', 'W31')
    row('W31', 0, 0, 'L', 'H1')
    # flag 0: the park is gone, so C0-3 is the blank just left of the gap
    row('SW0', 0, 0, 'R', 'W10')
    row('W10', 1, 1, 'R', 'W10')
    row('W10', 0, 0, 'R', 'W20')
    row('W20', 1, 1, 'R', 'W10')
    row('W20', 0, 0, 'L', 'W30')
    row('W30', 0, 0, 'L', 'H0')


def absorb():
    """The p==0, L=4, non-bottom pred: delete the top run and add one wrap.

    Entry AB0 with the head on E-4 (the separator), the run at E-3..E and the
    old index at E+3..E+2+n.  The new top run ends at E-5, the new index is
    n+1 marks at E-2..E+n-2, and p becomes 1.

    The index is shifted left four, with the extra index mark written first at
    E-2 as a sentinel.  The shuttle moves the source marks right-to-left?  No:
    left-to-right, target always four cells left of the source, and the written
    target block supplies the "walk left until a mark" stop.  The last source is
    detected by its right neighbour being blank, so no source sentinel is
    needed.
    """
    row('AB0', 0, 0, 'R', 'AB1')           # E-4: onto the run
    row('AB1', 1, 0, 'R', 'AB1')           # erase the four marks
    row('AB1', 0, 0, 'L', 'SB')            # E+1 blank: back onto E, then left
    row('SB', 0, 0, 'L', 'SB')             # over the erased run
    row('SB', 1, 1, 'R', 'R1')             # E-5: the run below's last mark
    row('R1', 0, 0, 'R', 'R2')             # E-4
    row('R2', 0, 0, 'R', 'R3')             # E-3
    row('R3', 0, 1, 'R', 'B')              # E-2: the index's bump mark
    row('B', 0, 0, 'R', 'B')               # over the gap
    row('B', 1, 1, 'R', 'SCB')             # X; the next cell is the source's 2nd
    row('SCB', 1, 1, 'L', 'S0')            # more source: erase this one
    row('SCB', 0, 0, 'L', 'S0L')           # blank right: this is the last source
    row('S0', 1, 0, 'L', 'SL')             # erase a source mark
    row('S0L', 1, 0, 'L', 'SLB')           # erase the last source mark
    row('SL', 0, 0, 'L', 'SL')             # left over the holes to the target block
    row('SL', 1, 1, 'R', 'SW')             # the last written target: step on t
    row('SW', 0, 1, 'R', 'SR')             # write the shifted mark
    row('SR', 0, 0, 'R', 'SR')             # right over the holes to the next source
    row('SR', 1, 1, 'R', 'SCB')            # source; test its right neighbour
    row('SLB', 0, 0, 'L', 'SLB')
    row('SLB', 1, 1, 'R', 'SWL')
    row('SWL', 0, 1, 'L', 'HOM')            # last shifted mark; home is left
    row('HOM', 1, 1, 'L', 'HOM')           # over the new index
    row('HOM', 0, 0, 'L', 'HOM1')          # E-3
    row('HOM1', 0, 0, 'L', 'HOM2')         # E-4
    row('HOM2', 1, 1, 'L', 'ABP0')         # absorb: E-5 is the run below
    row('HOM2', 0, 0, 'R', 'HEC')          # head-empty: back to C0
    row('HEC', 0, 0, 'L', 'CW1')           # and onto E_c = C0-1
    # grow the park at C0-3 (p 0 -> 1), then walk back with the spend's states
    row('ABP0', 1, 1, 'L', 'ABP0')         # over the chain below
    row('ABP0', 0, 0, 'L', 'ABP1')
    row('ABP1', 1, 1, 'L', 'ABP0')         # a single separator
    row('ABP1', 0, 0, 'L', 'ABP2')         # two blanks: C0-3
    row('ABP2', 0, 0, 'R', 'ABW0')         # p was 0: C0-2
    row('ABP2', 1, 1, 'L', 'ABP3')         # p >= 1: over the park
    row('ABP3', 1, 1, 'L', 'ABP3')
    row('ABP3', 0, 1, 'R', 'SW1')          # Lp-1: write the new park mark
    row('ABW0', 0, 0, 'L', 'ABW1')         # back to C0-3
    row('ABW1', 0, 1, 'R', 'SW1')          # write the park mark; SW1 walks home


def absorb_three():
    """The normalise loop's other arm: a plain 1 above the bottom.

    A chain may carry trailing plain-1 entries that `normalise` would fold into
    the wrap count.  After a 4-run absorb the new top can be one of them; the
    dispatch's L=3 state then checks the cell below and re-enters here.

    This arm must *not* bump the index: it is the model's normalise, not a
    pred.  The old index has n marks at E+3..E+2+n, the new one has n marks at
    E-1..E+n-2.  The leftmost old mark is therefore consumed to make room for
    the new sentinel at E-1, and the remaining n-1 marks shift left four.
    """
    row('AB0T', 0, 0, 'R', 'AB1T')         # E-3: onto the run
    row('AB1T', 1, 0, 'R', 'AB1T')         # erase the three marks
    row('AB1T', 0, 0, 'L', 'SB3')          # E+1 blank: back onto E, then left
    # find the run below and write the new sentinel at E-1
    row('SB3', 0, 0, 'L', 'SB3')           # over the erased run
    row('SB3', 1, 1, 'R', 'R13')           # E-4: the run below's last mark
    row('R13', 0, 0, 'R', 'R23')           # E-3
    row('R23', 0, 0, 'R', 'R33')           # E-2
    row('R33', 0, 1, 'R', 'BT3')           # E-1: the sentinel / new X
    # walk to the old X (E+3), consume it, then shift the rest with offset 4
    row('BT3', 0, 0, 'R', 'BT3')           # E, E+1, E+2
    row('BT3', 1, 0, 'R', 'SC4')           # E+3: the leftmost old mark, used up
    row('SC4', 1, 1, 'R', 'SCB')           # E+4: a next source; test s+1
    row('SC4', 0, 0, 'L', 'SE3')           # n == 1: no source left
    row('SE3', 0, 0, 'L', 'SE3')           # back over the gap to the sentinel
    row('SE3', 1, 1, 'L', 'HOM')           # E-1: the sentinel; HOM walks home


def unit_fold():
    """Fold a trailing plain-1 entry into the wrap count.

    A1/B1 reach AUX when the top run is a single mark.  If E-2 is also blank
    the chain is the singleton [ATOM] and the fs-limit follows; if E-2 is a
    mark the chain is head ++ [1], and

        w^p(w^head) = w^(p+1)(head),

    so the unit is erased, the park grows by one through the absorb's ABP walk,
    and the shared SW1 walk-back lands on the new top (E-2) in H1.  The erased
    cell leaves a second blank after the chain, which is exactly what the
    SW1/W21/W31 walk stop expects.
    """
    row('AUX', 0, 0, 'R', 'AUX0')          # E-2 blank: the singleton atom
    row('AUX0', 0, 0, 'R', 'FL0')          # E-1 -> E: the fs-limit
    row('AUX', 1, 1, 'R', 'N0')            # E-2 mark: a trailing unit at E
    row('N0', 0, 0, 'R', 'N1')             # E-1 -> E
    row('N1', 1, 0, 'L', 'N2')             # erase the unit
    row('N2', 0, 0, 'L', 'ABP0')           # E-1 -> E-2: the new top's last mark


def head_empty():
    """The H1 L=3 arm: [NUM(1)] -> [NUM(n+1)], then spend.

    Erase the three marks at C0, shift the index left three (its new start is
    C0+2), then enter the copy at CW1 with E_c = C0-1: the copy writes the
    n+3-mark run at C0..C0+n+2 and the n-mark index at C0+n+5.., exactly the
    head-empty target.  The copy's own finish goes to the spend.
    """
    row('HE0', 0, 0, 'R', 'HE1')           # C0-1: onto the run
    row('HE1', 1, 0, 'R', 'HE1')           # erase the three marks
    row('HE1', 0, 0, 'R', 'HE2')           # C0+3
    row('HE2', 0, 0, 'R', 'HS')            # C0+4 -> C0+5: first source mark
    row('HS', 1, 1, 'R', 'HST')            # test the source's right neighbour
    row('HST', 1, 1, 'L', 'HS0')           # more sources follow
    row('HST', 0, 0, 'L', 'HS0L')          # n == 1: this source is also the last
    row('HS0', 1, 0, 'L', 'HL1')           # erase, walk left three
    row('HL1', 0, 0, 'L', 'HL2')           # C0+4
    row('HL2', 0, 0, 'L', 'HSW')           # C0+3 -> C0+2: the first target
    row('HSW', 0, 1, 'R', 'SR')            # write it; the shared shuttle continues
    row('HS0L', 1, 0, 'L', 'HL1L')         # erase the only source
    row('HL1L', 0, 0, 'L', 'HL2L')         # C0+4
    row('HL2L', 0, 0, 'L', 'SWL')          # C0+3 -> C0+2: write and go home


def fs_limit():
    """[ATOM] with p wraps -> [NUM(1)] with p+n wraps (the index is unchanged).

    Pass 1 extends the atom to three marks and shifts the index right two
    (right-to-left, so the target two cells right is always an already-erased
    source).  Pass 2 walks the shifted index right-to-left; each source mark
    funds one park mark at the park's left end.  A hole is the first blank after
    the remaining prefix, so the return from the park needs no counter.
    """
    # --- pass 1: run C0..C0+2, index C0+5.. ---
    # This is a right-to-left shift by two of the index.  At each source s the
    # head erases s, walks right two, writes the shifted mark, walks left to s,
    # and continues with s-1.  FS5's 0 case writes the run's third mark at
    # C0+2 and hands over to the walk to the new index.
    row('FL0', 1, 1, 'R', 'FL1')           # C0+1
    row('FL1', 0, 1, 'R', 'FL2')           # write the second run mark
    row('FL2', 0, 0, 'R', 'FL3')           # C0+2 -> C0+3: first source
    row('FL3', 1, 1, 'R', 'FL3')           # to the old index's right end
    row('FL3', 0, 0, 'L', 'FSRC')
    row('FSRC', 1, 0, 'R', 'FS1')          # erase the source, go to s+2
    row('FS1', 0, 0, 'R', 'FS2')           # s+1
    row('FS2', 0, 1, 'L', 'FS3')           # s+2: the shifted mark
    row('FS3', 0, 0, 'L', 'FS4')           # s+1 (always blank)
    row('FS4', 0, 0, 'L', 'FS5')           # s (erased)
    row('FS5', 1, 0, 'R', 'FS1')           # next source: erase and shift
    row('FS5', 0, 1, 'R', 'FLP')           # done: write C0+2, enter pass 2
    row('FLP', 0, 0, 'R', 'FLP1')          # C0+3 -> C0+4
    row('FLP1', 0, 0, 'R', 'FLP2')         # C0+4 -> C0+5
    row('FLP2', 1, 1, 'R', 'FLP2')         # over the new index
    row('FLP2', 0, 0, 'L', 'P3')           # onto its rightmost mark

    # --- pass 2: one park mark per index mark, index preserved ---
    # One trip per mark, right to left.  The current mark is erased first, so
    # on the way back the first blank after the remaining prefix is exactly the
    # hole; QII restores it and steps onto the next mark.  QIN's blank case is
    # the end: everything has been restored and the index is whole again.
    row('P3', 1, 0, 'L', 'QIL')            # erase the source
    row('QIL', 1, 1, 'L', 'QIL')           # over the remaining index prefix
    row('QIL', 0, 0, 'L', 'QIG')           # C0+4
    row('QIG', 0, 0, 'L', 'QIR')           # C0+3 -> C0+2: the run
    row('QIR', 1, 1, 'L', 'QIR')           # over the run
    row('QIR', 0, 0, 'L', 'QIB')           # C0-1
    row('QIB', 0, 0, 'L', 'QIP')           # C0-2 -> C0-3
    row('QIP', 0, 1, 'R', 'QIK')           # park empty: write at C0-3
    row('QIP', 1, 1, 'L', 'QIW')           # over the park
    row('QIW', 1, 1, 'L', 'QIW')
    row('QIW', 0, 1, 'R', 'QIK')           # write left of the park
    row('QIK', 1, 1, 'R', 'QIK')           # back over the park
    row('QIK', 0, 0, 'R', 'QIG2')          # C0-2
    row('QIG2', 0, 0, 'R', 'QIR2')         # C0-1 -> C0
    row('QIR2', 1, 1, 'R', 'QIR2')         # over the run
    row('QIR2', 0, 0, 'R', 'QIG3')         # C0+3
    row('QIG3', 0, 0, 'R', 'QII')          # C0+4 -> C0+5
    row('QII', 1, 1, 'R', 'QII')           # over the index prefix
    row('QII', 0, 1, 'L', 'QIN')           # the hole: restore, step onto the next
    row('QIN', 1, 0, 'L', 'QIL')           # another source: erase and repeat
    row('QIN', 0, 0, 'L', 'QIH')           # none left: C0+3
    row('QIH', 0, 0, 'L', 'H1')            # C0+2: home


def build():
    """Blank tape -> (p=3, chain=[ATOM1], n=3), home H1 on E=6.

    This is eps_1[3]: three wraps over eps_0+1.  The smallest geometry that
    holds three park marks is C0=5 (Rp=2), so the pattern on cells 0..11 is

        1 1 1 0 0 1 1 0 0 1 1 1
        park    run    index

    The head starts at cell 0; the walk back stops on the first blank of the
    two-blank gap and steps to E=6 in H1.  The build state is the first state,
    so a blank-tape run starts at state 0 as usual.
    """
    row('BU0', 0, 1, 'R', 'BU1')           # cell 0: park
    row('BU1', 0, 1, 'R', 'BU2')           # 1
    row('BU2', 0, 1, 'R', 'BU3')           # 2: Rp
    row('BU3', 0, 0, 'R', 'BU4')           # 3: first gap blank
    row('BU4', 0, 0, 'R', 'BU5')           # 4
    row('BU5', 0, 1, 'R', 'BU6')           # 5: C0, ATOM1
    row('BU6', 0, 1, 'R', 'BU7')           # 6: E
    row('BU7', 0, 0, 'R', 'BU8')           # 7: first gap blank
    row('BU8', 0, 0, 'R', 'BU9')           # 8
    row('BU9', 0, 1, 'R', 'BU10')          # 9: X = E+3
    row('BU10', 0, 1, 'R', 'BU11')         # 10
    row('BU11', 0, 1, 'L', 'BW1')          # 11: last index mark
    row('BW1', 1, 1, 'L', 'BW1')           # back over the index
    row('BW1', 0, 0, 'L', 'BW2')           # first gap blank
    row('BW2', 0, 0, 'L', 'H1')            # onto E


def build_table():
    """Assemble the whole table (the limit moves are appended below)."""
    TBL.clear()
    SID.clear()
    SNAME.clear()
    build()
    copy_routine()
    dispatch_and_pred()
    pred_shorten()
    erase_for_copy()
    spend()
    absorb()
    absorb_three()
    unit_fold()
    head_empty()
    fs_limit()
    return machine()


def valnum(e):
    """The numeric value of a run entry (an Ord number or a bare int)."""
    return e.terms[0][1] if isinstance(e, Ord) else e


def want_copy(chain, n):
    """What the copy must produce: the chain after an fs-successor.

    The fs-successor is head ++ [n+1] with head = chain-1, and the caller has
    already applied the decrement to the tape, so the model side applies it here.
    """
    return chain[:-1] + [NUM(valnum(chain[-1]) - 1), n + 1]


def run_to(t, head, state, tape, stop, limit=20_000_000):
    """Step until `state` is one of `stop` (before stepping it) or the machine halts."""
    steps = 0
    while steps < limit:
        if state in stop:
            return steps, tape, head, state, False
        r = t.step(tape, head, state)
        steps += 1
        if r is None:
            return steps, tape, head, state, True
        head, state = r
    return steps, tape, head, state, False


def home_of(p):
    return 'H0' if p == 0 else 'H1'


def plain_chain(chain):
    """Decoded run entries -> the chain values the model multiplies.

    A decoded NUM(c) is the same run as the plain int c; keeping it as an Ord
    would make `val` pass an Ord as a coefficient.  ATOM and ATOM1 are not
    numbers and stay as they are.
    """
    out = []
    for e in chain:
        if isinstance(e, Ord):
            if e.is_atom() or e == ATOM1:
                out.append(e)
            else:
                out.append(e.terms[0][1])
        else:
            out.append(e)
    return out


def check_moves(trials=400, moves=4, seed=13):
    """Home-to-home against `eps1_chain.step`, comparing ordinal values.

    The machine may land on a value-correct but not-yet-normalised home (the
    absorb leaves the trailing unit stacks for the next dispatch's B3A arm), so
    the comparison is on `full`, never on the raw shape.  Consecutive moves run
    from the machine's own tape, which is the stronger check.
    """
    import random
    rng = random.Random(seed)
    starts = [
        (0, [ATOM], 3), (0, [ATOM1], 3), (0, [NUM(1)], 3),
        (0, [NUM(2)], 3), (0, [NUM(1), 2], 3), (0, [ATOM, 2], 3),
        (0, [NUM(2), 2], 3), (0, [NUM(1), 1, 2], 3),
        (1, [ATOM], 3), (1, [ATOM1], 3), (1, [NUM(1)], 3),
        (2, [ATOM], 4), (3, [NUM(1)], 3), (2, [NUM(2), 2], 4),
    ]
    for _ in range(trials):
        bottom = rng.choice([ATOM, ATOM1, NUM(1), NUM(2), NUM(3)])
        chain = [bottom] + [rng.choice([2, 3, 4])
                            for _ in range(rng.randint(0, 2))]
        starts.append((rng.randint(0, 3), chain, rng.randint(1, 5)))

    t = machine()
    homes = {SID['H0'], SID['H1']}
    bad = 0
    for p, chain, n in starts:
        tape, E, home = frame(p, chain, n)
        head, st = E, SID[home]
        cur = (p, list(chain), n)
        ok, why = True, ''
        for mv in range(moves):
            if not cur[1]:
                break
            want = C.step(*cur)[:3]
            want_zero = not want[1]
            wv = C.full(want[0], plain_chain(want[1]))
            cv = C.full(cur[0], plain_chain(cur[1]))
            advanced = False
            extra = 0
            while True:
                steps = 0
                halted = False
                while steps < 2_000_000:
                    r = t.step(tape, head, st)
                    steps += 1
                    if r is None:
                        halted = True
                        break
                    head, st = r
                    if st in homes:
                        break
                else:
                    ok, why = False, f'move {mv + 1}: loop'
                    break
                if halted:
                    if want_zero:
                        advanced = True
                    else:
                        ok, why = False, (f'move {mv + 1}: machine halted, '
                                          f'model says {want}')
                    break
                try:
                    got = decode(tape, head)
                except Exception as e:                  # noqa: BLE001
                    ok, why = False, f'move {mv + 1}: decode: {e}'
                    break
                gv = C.full(got[0], plain_chain(got[1]))
                if got[2] == want[2] and gv == wv:
                    cur = want
                    advanced = True
                    break
                if got[2] == cur[2] and gv == cv:
                    # A value-neutral normalisation move (B3A absorbing a
                    # trailing unit run): the model folded this into the
                    # previous step, so do not advance the model here.
                    extra += 1
                    if extra > 40:
                        ok, why = False, (f'move {mv + 1}: normalisation loop '
                                          f'at {gv!r}')
                        break
                    continue
                ok, why = False, (f'move {mv + 1}: got {gv!r} (p={got[0]}, '
                                  f'n={got[2]}), want {wv!r}')
                break
            if not ok or (advanced and want_zero):
                break
            if not advanced:
                ok, why = ok, why or f'move {mv + 1}: no progress'
                break
        if not ok:
            bad += 1
            print(f'  p={p} chain={[str(x) for x in chain]} n={n}: {why}')
            if bad >= 10:
                print('  (stopping after 10 failures)')
                break
    print(f'  {len(starts)} starts x {moves} moves: '
          + ('ALL OK' if not bad else f'{bad} FAILURES'))
    return bad == 0


def check_halt_counts(cases=None, limit=2_000_000):
    """Advancing homes + the halt equal `eps1_chain.run`'s move count.

    A value-neutral home (the absorb's B3A fold, or the trailing-unit fold)
    appears in the machine but was folded into one model step, so it must not
    count as a move.  Compare the decoded ordinal values at consecutive homes.
    """
    cases = cases or [
        (0, [NUM(1)], 3), (0, [NUM(2)], 3), (0, [NUM(4)], 3),
        (0, [NUM(1), 2], 3), (0, [NUM(2), 2], 3),
        (0, [NUM(1), 1, 2], 3), (1, [NUM(1)], 3), (1, [NUM(2)], 3),
        (2, [NUM(1)], 3), (0, [NUM(2)], 1),
    ]
    print('halting counts against the model')
    bad = 0
    homes = {SID['H0'], SID['H1']}
    for p, chain, n in cases:
        tape, E, home = frame(p, chain, n)
        t = machine()
        head, st = E, SID[home]
        prev = C.full(p, plain_chain(list(chain)))
        trips = advancing = extra = steps = 0
        halted = False
        while steps < limit:
            r = t.step(tape, head, st)
            steps += 1
            if r is None:
                halted = True
                break
            head, st = r
            if st in homes:
                trips += 1
                got = decode(tape, head)
                gv = C.full(got[0], plain_chain(got[1]))
                if gv == prev:
                    extra += 1
                else:
                    advancing += 1
                    prev = gv
        mv, _ = C.run(p, list(chain), n, limit=10000)
        got = advancing + (1 if halted else 0)
        ok = halted and got == mv
        print(f'  p={p} chain={[str(x) for x in chain]} n={n}: '
              f'homes={trips} advancing={advancing} extra={extra} '
              f'halted={halted} count={got} model={mv} '
              f'{"PASS" if ok else "FAIL"}')
        bad += 0 if ok else 1
    print('  ' + ('ALL OK' if not bad else f'{bad} FAILURES'))
    return bad == 0


def check_build():
    """Blank tape, state 0: build eps_1[3] and land in H1."""
    print('blank tape -> eps_1[3]')
    t = machine()
    head, st, tape = 0, 0, {}
    homes = {SID['H0'], SID['H1']}
    steps = 0
    while steps < 10_000:
        r = t.step(tape, head, st)
        steps += 1
        if r is None:
            print(f'  HALT after {steps} steps (expected a home)')
            return False
        head, st = r
        if st in homes:
            got = decode(tape, head)
            ok = same(got, (3, [ATOM1], 3))
            print(f'  steps={steps} home={SNAME[st]} got={got} '
                  f'{"PASS" if ok else "FAIL"}')
            return ok
    print('  loop')
    return False


def check_copy(cases=(1, 2, 3, 4, 5, 8, 13, 21)):
    """The copy in isolation, on the tape the fs-successor hands it."""
    print('the index copy, in isolation')
    bad = 0
    for n in cases:
        chain = [NUM(1), 3]                 # top entry 3, so the decrement leaves 2
        p = 1
        tape, E, _ = frame(p, chain, n)
        tape[E] = 0                         # the fs-successor's decrement
        t = tm.TM(len(SID), dict(TBL))
        steps, t2, h2, s2, halted = run_to(t, E - 1, SID['CW0'], tape,
                                           {SID['SP0']})
        ok, why = False, ''
        if not halted and s2 != SID['SP0']:
            why = 'did not reach the spend'
        else:
            try:
                got = decode(t2, h2)
            except Exception as e:                  # noqa: BLE001
                got, why = None, f'decode: {e}'
            if got is not None:
                ok = same(got, (p, want_copy(chain, n), n))
                if not ok:
                    why = f'got p={got[0]} chain={[str(x) for x in got[1]]} n={got[2]}'
        print(f'  n={n:<3} steps={steps:<7} {"PASS" if ok else "FAIL " + why}')
        if not ok:
            print('      want', [str(x) for x in want_copy(chain, n)])
            print('      tape', tm.tape_str(t2, h2))
            bad += 1
    print('ALL OK' if not bad else f'{bad} FAILURES')
    return bad == 0


def check_copy_random(trials=60, seed=5):
    """The copy on random shapes: how many entries, how big the top entry."""
    import random
    print('the copy on random chain shapes')
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        chain = [NUM(rng.randint(1, 3))] + [rng.randint(2, 4) for _ in range(rng.randint(0, 2))]
        if len(chain) == 1 and chain[0] == NUM(1):
            chain = [NUM(2)]        # [NUM(1)] is the head-empty case, not this path
        p = rng.randint(0, 3)
        n = rng.randint(1, 7)
        tape, E, _ = frame(p, chain, n)
        tape[E] = 0
        t = tm.TM(len(SID), dict(TBL))
        steps, t2, h2, s2, halted = run_to(t, E - 1, SID['CW0'], tape,
                                           {SID['SP0']})
        ok, why = False, ''
        if not halted and s2 != SID['SP0']:
            why = 'did not reach the spend'
        else:
            try:
                got = decode(t2, h2)
            except Exception as e:                  # noqa: BLE001
                got, why = None, f'decode: {e}'
            if got is not None:
                ok = same(got, (p, want_copy(chain, n), n))
                if not ok:
                    why = f'got p={got[0]} chain={[str(x) for x in got[1]]} n={got[2]}'
        if not ok:
            print(f'  p={p} chain={chain} n={n}: {why}')
            bad += 1
    print(f'  {trials} random shapes: ' + ('OK' if not bad else f'{bad} FAILURES'))
    return bad == 0


if __name__ == '__main__':
    build_table()
    ok = check_build()
    ok = check_copy() and ok
    ok = check_copy_random() and ok
    ok = check_moves() and ok
    ok = check_halt_counts() and ok
    print('states used:', len(SID), ' rows:', len(TBL))
    sys.exit(0 if ok else 1)
