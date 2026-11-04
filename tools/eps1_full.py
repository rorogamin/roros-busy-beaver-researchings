"""The eps_1 tower machine: the whole descent as a 2-symbol table.

`tools/tower_free.py` is the semantics -- state (park m, working part W) and what
one move does to it.  `tools/eps1_tower.py` built a writer that copies n from an
index; this module does not need one: n is a *constant* of the machine, so move B
writes n+1 marks with a fixed chain of states, and the index, its copy and the
whole leftward drift disappear.

## Frame

    [free]  1^m (park)  [gap 2]  1^{W_0} 0 1^{W_1} 0 ... 0 1^{W_k}  [free]

W is held bottom-first, so its top run -- the one move B replaces with n+1 and
move A decrements -- is the rightmost run and always grows into free space.  The
park is a unary count held at the far left.  It is not part of the tower: it is
the number of leading 1s the tower carries, and it only shrinks during the
descent except when a leading 1 folds into it.

Two invariants, both kept by construction:

  * while m >= 1, the park's rightmost mark sits exactly three cells left of W's
    leftmost mark, so the gap is two blanks and "is there a park" is a three-cell
    look.  Spending erases the park's *leftmost* mark and folding writes at its
    *leftmost minus one*, so its right end never moves;
  * gaps inside W are one blank and free space at either end is two or more, so
    walking a run and peeking past a blank says whether it was a gap or an end.

## The routines

`HN` and `HE` are the two loop heads.  `HN` is the head on W's leftmost mark (W
nonempty); `HE` is the head on the park's rightmost mark (W empty -- only reachable
with a park, so it always exists).  Every move is a trip from one home back to a
home, so moves can be counted and the tape decoded between them.

    HN    has a park ?  B : A
    A     erase W's top run's rightmost mark, then fold leading 1s
    B     spend a level, write n+1 as W's new top run, erase the rightmost mark
          of the run below it
    HE    W is empty: look three cells right.  A mark is W, so go to HN.  Blank
          is the "chain is 1^m" case: spend once (gone => the chain was 1, halt),
          spend again, then write n+1 as the whole of W
    fold  park += 1 and erase the single mark of W's top run, then back to HE
"""

import sys

sys.path.insert(0, 'tools')
import tm
import tower_free as TF

NAME = {}
NUM = {}
TBL = {}


def S(name):
    if name not in NUM:
        NUM[name] = len(NUM)
        NAME[NUM[name]] = name
    return NUM[name]


def row(st, sym, w, d, nxt):
    k = (S(st), sym)
    assert k not in TBL, f'duplicate row {st},{sym}'
    TBL[k] = (w, d, None if nxt is None else S(nxt))


def machine():
    return tm.TM(len(NUM), dict(TBL))


HALT = 'HALT'          # no rows: the machine stops here


# --- routines ----------------------------------------------------------------

def spend(tag, ok, gone):
    """Erase the park's leftmost mark.

    Entry: the head on any park mark (it walks left to the leftmost).  Exit `ok`:
    the head on the park's new leftmost mark; `gone`: the head one cell right of
    the erased cell, with nothing left of the park.  The right end never moves,
    which is what keeps the gap at two blanks.
    """
    a = f'SP{tag}'
    row(a, 1, 1, 'L', a)                  # over the park
    row(a, 0, 0, 'R', a + 'b')            # off its left end: step back onto it
    row(a + 'b', 1, 0, 'L', a + 'c')      # erase the leftmost
    row(a + 'b', 0, 0, 'R', a + 'c')      # (cannot happen)
    row(a + 'c', 0, 0, 'R', a + 'd')      # back onto the erased cell
    row(a + 'd', 0, 0, 'R', a + 'e')      # one right: a mark means it survives
    row(a + 'e', 1, 1, 'L', a + 'f')
    row(a + 'e', 0, 0, 'R', gone)
    row(a + 'f', 0, 0, 'R', ok)           # rewind onto the new leftmost


def walk_to_w(tag, target):
    """Right from the park (or from its empty slot) to W's leftmost.

    Over the park's marks, then over the blanks that follow, then rewind onto the
    first mark: that is W's leftmost whether the park still has levels, has just
    been emptied, or has none at all.
    """
    a = f'GW{tag}'
    row(a, 1, 1, 'R', a)                  # over what is left of the park
    row(a, 0, 0, 'R', a + 'b')            # a blank: cross the separator
    row(a + 'b', 1, 1, 'L', a + 'c')      # the first mark: W's leftmost
    row(a + 'b', 0, 0, 'R', a + 'b')      # another blank
    row(a + 'c', 0, 0, 'R', target)       # rewind onto it


def dispatch_and_move_a():
    """`HN`: is there a park?  Then A -- erase W's top run's rightmost mark.

    Entry and exit: `HN`.
    """
    row('HN', 1, 1, 'L', 'D1')
    row('D1', 0, 0, 'L', 'D2')
    row('D1', 1, 1, 'L', 'D2')            # (the gap is two: defensive)
    row('D2', 0, 0, 'L', 'D3')
    row('D2', 1, 1, 'L', 'D3')
    row('D3', 1, 1, 'L', 'SPB')           # a park: B, and the spend starts here
    row('D3', 0, 0, 'R', 'D4')            # no park: back to W's leftmost
    row('D4', 0, 0, 'R', 'D5')
    row('D4', 1, 1, 'R', 'D5')
    row('D5', 0, 0, 'R', 'A1')
    row('D5', 1, 1, 'R', 'A1')
    # --- A proper
    row('A1', 1, 1, 'R', 'A1')            # over W's runs
    row('A1', 0, 0, 'R', 'AW')            # one past the first blank
    row('AW', 1, 1, 'R', 'A1')            # that blank was an inside gap
    row('AW', 0, 0, 'L', 'AB')            # free space: back onto the first blank
    row('AB', 0, 0, 'L', 'A2')            # and onto the top run's last mark
    row('A2', 1, 0, 'L', 'A3')            # erase it
    row('A2', 0, 0, 'R', HALT)            # (cannot happen: W is not empty)
    row('A3', 1, 1, 'L', 'A4')            # the run still has a mark
    row('A3', 0, 0, 'R', HALT)            # (cannot happen: W[0] >= 2)
    row('A4', 0, 0, 'R', 'F1')            # exactly one mark left: fold it
    row('A4', 1, 1, 'L', 'LWM')           # two or more: A is done


def fold():
    """park += 1 and erase W's single top mark; ends at `HE`.

    Entered at `last`, the mark to erase.  The new park mark goes one cell left of
    the park's leftmost mark when there is a park, and three cells left of W's
    leftmost mark when there is not -- which is the only way a park is created.
    """
    row('F1', 1, 0, 'L', 'F2')            # erase the single mark, step left
    row('F1', 0, 1, 'R', HALT)            # (cannot happen)
    row('F2', 0, 0, 'L', 'F3')            # last-1 is a gap or their separator; look at last-2
    row('F2', 1, 1, 'R', HALT)            # (cannot happen: the run was one mark)
    row('F3', 1, 1, 'L', 'FOV')           # W nonempty
    row('F3', 0, 0, 'L', 'FSX')           # W empty: last-3 is the park's right end
    row('FOV', 1, 1, 'L', 'FOV')          # over W's runs
    row('FOV', 0, 0, 'L', 'FPE')
    row('FPE', 1, 1, 'L', 'FOV')          # one blank: an inside gap
    row('FPE', 0, 0, 'L', 'FSX')          # two: the separator, at W's left minus two
    row('FSX', 1, 1, 'L', 'FPK')          # a park: walk left over it
    row('FSX', 0, 1, 'L', 'FNR')          # none, or W empty: this cell is the write
    row('FNR', 0, 0, 'R', 'HE')           # rewind onto the new mark
    row('FPK', 1, 1, 'L', 'FPK')
    row('FPK', 0, 1, 'R', 'FRU')          # the blank left of it: write, step right
    row('FRU', 1, 1, 'R', 'FRU')          # back over the park
    row('FRU', 0, 0, 'L', 'HE')           # one past its right end: rewind


def normalise():
    """Fold W's top run into the park while it is a single mark.

    `tower_free` re-splits at every step, and the split is what turns a leading 1
    into a park level.  On tape that has to be done eagerly: a park level is a
    physical mark.  Entry `NW1`: the head on W's leftmost mark.
    """
    row('NW1', 1, 1, 'R', 'NW1')          # over W's runs
    row('NW1', 0, 0, 'R', 'NW2')          # one past the first blank
    row('NW2', 1, 1, 'R', 'NW1')          # that blank was an inside gap
    row('NW2', 0, 0, 'L', 'NT0')          # free space: back onto the first blank
    row('NT0', 0, 0, 'L', 'NT1')          # and onto the top run's last mark
    row('NT1', 1, 1, 'L', 'NT2')          # step left, and look at last-1
    row('NT2', 1, 1, 'L', 'LWM')          # two or more marks: nothing to fold
    row('NT2', 0, 0, 'R', 'F1')           # exactly one: onto it, and the fold erases


def push_top(tag, n):
    """Move B's write: one mark off W's top run, then n+1 marks as the new top.

    The order matters.  `tower_free` gives W' = [n+1, W[0]-1] ++ W[1:], i.e. the
    old top loses a mark and a new top of n+1 appears above it.  Decrementing a
    run in the middle of W would leave two blanks where its last mark was, and a
    two-blank gap is the separator; doing it while the run is still the top costs
    nothing, because the cell it frees is at the free end.
    """
    a = f'BW{tag}'
    row(a, 1, 1, 'R', a)                  # over W's runs
    row(a, 0, 0, 'R', a + 'b')            # one past the first blank
    row(a + 'b', 1, 1, 'R', a)            # that blank was an inside gap
    row(a + 'b', 0, 0, 'L', a + 'c')      # free space: back onto the first blank
    row(a + 'c', 0, 0, 'L', a + 'd')      # and onto the top run's last mark
    row(a + 'd', 1, 0, 'R', f'{a}w1')     # one mark off the top run
    row(a + 'd', 0, 1, 'R', f'{a}w1')     # (cannot happen)
    prev = f'{a}w1'
    for i in range(1, n + 2):
        nxt = f'BK{tag}' if i == n + 1 else f'{a}w{i+1}'
        row(prev, 0, 1, 'R', nxt)
        prev = f'{a}w{i+1}'
    row(f'BK{tag}', 0, 0, 'L', 'LWM')     # onto the new top run, then HOME


def walk_to_hn():
    """`LWM`: left from inside W to `HN`."""
    row('LWM', 1, 1, 'L', 'LWM')
    row('LWM', 0, 0, 'L', 'LWP')
    row('LWP', 1, 1, 'L', 'LWM')          # one blank: an inside gap
    row('LWP', 0, 0, 'R', 'LWQ')          # two: the separator
    row('LWQ', 0, 0, 'R', 'HN')           # W's leftmost is one more


def home_e(n, write_entry):
    """`HE`: the head on the park's rightmost mark, W empty."""
    row('HE', 1, 1, 'R', 'HE1')           # look three right for W
    row('HE1', 0, 0, 'R', 'HE2')
    row('HE1', 1, 1, 'R', HALT)           # (cannot happen: the gap is two)
    row('HE2', 0, 0, 'R', 'HE3')
    row('HE2', 1, 1, 'R', HALT)
    row('HE3', 1, 1, 'L', 'HEN')          # W: go back to `HN`
    row('HE3', 0, 0, 'L', 'HXL')          # the chain is 1^m: spend it down
    row('HEN', 0, 0, 'R', 'NW1')         # W: fold any leading 1 first
    row('HXL', 0, 0, 'L', 'HXL')          # back over the blanks
    row('HXL', 1, 1, 'L', 'SPE1')         # the park's rightmost
    spend('E1', 'SPE2', HALT)             # one level; gone means the chain was 1
    spend('E2', 'PWE', 'PWE')             # the second level
    row('PWE', 1, 1, 'R', 'PWE')          # W is empty: walk out and write
    row('PWE', 0, 0, 'R', 'PWF')          # at the first blank
    row('PWF', 0, 0, 'R', write_entry)     # the third is the run's first cell
    # the marks themselves, and the way home, are `push_top`'s


def build(h):
    """Blank tape -> a park of `h` levels, head on its rightmost mark."""
    prev = 'B0'
    for i in range(h):
        nxt = f'B{i+1}' if i < h - 1 else 'BE'
        row(prev, 0, 1, 'R', nxt)
        prev = f'B{i+1}'
    row('BE', 0, 0, 'L', 'HE')            # onto the last mark


def build_table(n=2, h=3):
    TBL.clear()
    NUM.clear()
    NAME.clear()
    dispatch_and_move_a()
    fold()
    normalise()
    walk_to_hn()
    spend('B', 'GWB', 'GWB')              # B's spend, then over to W
    walk_to_w('B', 'BWB')                 # to W's leftmost, then out to its top
    push_top('B', n)
    home_e(n, 'BWBw1')
    build(h)
    return machine()


# --- the frame and the reference step -----------------------------------------

def frame(m, W, park_at=4):
    """Tape for (park m, W bottom-first), head on the home mark."""
    tape = {}
    if m:
        for i in range(m):
            tape[park_at + i] = 1
        wl = park_at + m - 1 + 3
    else:
        wl = park_at + 3
    p = wl
    for k, w in enumerate(W):
        if k:
            p += 1
        for i in range(w):
            tape[p + i] = 1
        p += w
    if W:
        return tape, wl, 'HN'
    return tape, park_at + m - 1, 'HE'


def ref_move(m, W, n):
    """`tower_free`'s move, on (park, W bottom-first).  None means halt."""
    T = [1] * m + list(reversed(W))
    T2 = TF.step(T, n)
    if T2 is None:
        return None
    m2, Wm = TF.split(T2)
    return m2, list(reversed(Wm))


def decode(tape, head, home):
    """Tape -> (park m, W bottom-first), given the home state's head.

    The gap is one or two blanks, so the park's right end is at most three cells
    left of W's leftmost mark; and `HE` only says the head is on the park's right
    end, not that W is empty, because every fold lands there.
    """
    if tape.get(head) != 1:
        raise ValueError(f'{home} but no mark under the head')
    if home == 'HN':
        wl = head
        q = head - 1
        seen = 0
        while seen < 3 and tape.get(q) != 1:
            q -= 1
            seen += 1
        m = 0
        if tape.get(q) == 1:
            while tape.get(q - 1) == 1:
                q -= 1
            e = q
            while tape.get(e) == 1:
                e += 1
            m = e - q
    else:
        q = head
        while tape.get(q - 1) == 1:
            q -= 1
        m = head - q + 1
        wl = None                        # HE is only a home with W empty
    W = []
    if wl is not None:
        p = wl
        while True:
            ln = 0
            while tape.get(p) == 1:
                ln += 1
                p += 1
            W.append(ln)
            if tape.get(p + 1) == 1:
                p += 1
                continue
            break
    return m, W


HOMES = set()


def at_home(tape, head, state):
    """Is this a state the model can be in?  -> 'HN', 'HE', or None.

    `HN` always is.  `HE` (a fold just landed on the park's right end) is a model
    state only when W is empty: if a leading 1 is still there, the normalisation
    is unfinished and the move continues.  The gap is exactly two blanks, so W's
    leftmost mark would be three cells right of the head.
    """
    if state == NUM['HN']:
        return 'HN'
    if state == NUM['HE'] and tape.get(head + 3) != 1:
        return 'HE'
    return None


def run_move(t, tape, head, state, limit=400000):
    """Run until the machine reaches a model state or stops."""
    tape = dict(tape)
    steps = 0
    while steps < limit:
        r = t.step(tape, head, state)
        steps += 1
        if r is None:
            return steps, tape, head, state, True
        head, state = r
        if at_home(tape, head, state):
            return steps, tape, head, state, False
    return steps, tape, head, state, False


# --- checks -------------------------------------------------------------------

def check_moves(n=2, verbose=False):
    print(f'move-by-move against tower_free (base n={n})')
    t = build_table(n=n)
    bad = 0
    cases = [(0, [2]), (0, [3]), (0, [2, 2]), (0, [1, 2]), (1, [2]),
             (2, [2]), (2, [1, 1, 2]), (3, [2, 2]), (2, []), (1, []), (5, []),
             (0, [2, 2, 2]), (4, [1, 2]), (1, [3, 2]), (0, [4]), (1, [2, 2])]
    for m, W in cases:
        tape, head, home = frame(m, W)
        state = NUM[home]
        cur = (m, list(W))
        trace = [cur]
        moves = 0
        ok = True
        while True:
            want = ref_move(cur[0], cur[1], n)
            steps, tape, head, state, halted = run_move(t, tape, head, state)
            moves += 1
            if want is None:
                if not halted:
                    ok = False
                    print(f'  m={m} W={W}: model says halt, machine continues')
                break
            if halted:
                ok = False
                print(f'  m={m} W={W}: machine halted, model says {want}')
                break
            got = decode(tape, head, at_home(tape, head, state))
            cur = want
            trace.append(got)
            if got != want:
                ok = False
                print(f'  m={m} W={W}: move {moves} got {got}, want {want}')
                print('      tape', tm.tape_str(tape, head))
                break
            if moves > 800:
                ok = False
                print(f'  m={m} W={W}: no halt in 800 moves')
                break
        print(f'  m={m} W={str(W):<10} moves={moves:<4} final={trace[-1]} '
              f'{"PASS" if ok else "FAIL"}')
        if not ok:
            bad += 1
        if verbose:
            print('     ', trace)
    print('ALL OK' if not bad else f'{bad} FAILURES')
    return bad == 0


def check_build(h=3, n=2):
    print(f'blank tape -> park of {h} -> descent -> halt')
    t = build_table(n=n, h=h)
    steps, tape, head, state, halted = t.run(head=0, state=NUM['B0'],
                                             tape={}, max_steps=50_000_000)
    marks = sum(1 for v in tape.values() if v == 1)
    print(f'  h={h} n={n} steps={steps} halted={halted} marks left={marks}')
    return halted


def count_run(t, n, h, limit=400_000_000):
    """Blank tape with a park of h levels -> (steps, moves, halted)."""
    tape, head, state = {}, 0, NUM['B0']
    steps = moves = 0
    while steps < limit:
        r = t.step(tape, head, state)
        steps += 1
        if r is None:
            return steps, moves, True
        head, state = r
        if at_home(tape, head, state):
            moves += 1
    return steps, moves, False


def check_scaling(n=2, hs=(1, 2, 3, 4, 5, 6, 7)):
    print(f'steps from a park of h levels (base n={n}); moves vs tower_free')
    bad = 0
    for h in hs:
        t = build_table(n=n, h=h)
        steps, moves, halted = count_run(t, n, h)
        want = TF.descent([1] * h, n, limit=10_000_000)[0]
        ok = halted and moves == want
        print(f'  h={h}: steps={steps:<12} moves={moves:<8} '
              f'tower_free moves={want:<8} {"PASS" if ok else "FAIL"}')
        if not ok:
            bad += 1
    print('ALL OK' if not bad else f'{bad} FAILURES')
    return bad == 0


if __name__ == '__main__':
    ok = check_moves()
    ok = check_scaling() and ok
    check_build()
    print('ALL OK' if ok else 'FAILURES')
    sys.exit(0 if ok else 1)
