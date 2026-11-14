#!/usr/bin/env python3
"""
uubin.py -- the greedy 0-indexed U.a.U-avoiding sequence on a directly built
two-symbol Turing machine (no virtual alphabet, no compiler layer).

Tape layout
-----------
A group is five cells:      0 m2 m1 m0 0
and a record (one sequence symbol v) is a group followed by

                            block = 1^(v+1)          (1..6 ones)

so the tape is

    gWALL  g0 block0  g1 block1  ...  g(n-1) block(n-1)  gEND

with marker values

    0 = plain   1 = WALL   2 = B   3 = illegal end   4 = A   6 = W   7 = END

Blocks are never empty, so "the cell right of a group" is always a 1: the
block's first cell ("bf") is an unambiguous place to stand, and four lefts
from bf is always the group's first marker bit.

The machine implements the literal rule

    w + c is illegal  iff  exists m >= 1 with
        w'[N-2m-1+t] == w'[N-m+t]   for t = 0..m-1     (N = len(w))

with two anchors (A on D_(N-2m-1), B on D_(N-m)) and two walkers (W) that
sweep the blocks being compared; a mismatch moves A two symbols left and B
one symbol left, which is exactly m -> m+1: no counter is needed, the search
simply runs off the left wall.  After an accepted candidate the machine reads
the record back and halts iff it is `halt_on`.  The shipped machine uses
halt_on = 5; whether a 5 ever occurs is open, so the machine is a cryptid.
halt_on is a parameter so the very same append/check/rollback machinery can
be shown to halt at the first 0, 1, 2, 3 ...
"""

import sys

sys.path.insert(0, '.')
from uu2tm import reference                        # noqa: E402

PLAIN, WALL, A, B, W, END, ILLEGAL = 0, 1, 4, 2, 6, 7, 3
BITS = {m: ((m >> 2) & 1, (m >> 1) & 1, m & 1) for m in
        (PLAIN, WALL, A, B, W, END, ILLEGAL)}


def group(m):
    return [0] + list(BITS[m]) + [0]


def start_tape():
    return group(WALL) + group(END)


# ---------------------------------------------------------------------------
class TM:
    def __init__(self):
        self.tr = {}

    def t(self, st, rd, wr, mv, nx):
        self.tr[(st, rd)] = (wr, mv, nx)

    def same(self, st, mv, nx):
        for b in (0, 1):
            self.t(st, b, b, mv, nx)

    def wr(self, st, w, mv, nx):
        for b in (0, 1):
            self.t(st, b, w, mv, nx)


def mchain(tm, tag, n, mv, cont):
    """n blind moves; the entry state is `tag` itself."""
    for i in range(n):
        st = tag if i == 0 else '%s#%d' % (tag, i)
        nx = cont if i + 1 == n else '%s#%d' % (tag, i + 1)
        tm.same(st, mv, nx)
    return tag


def wchain(tm, tag, bits, mv, cont):
    for i, b in enumerate(bits):
        st = tag if i == 0 else '%s#%d' % (tag, i)
        nx = cont if i + 1 == len(bits) else '%s#%d' % (tag, i + 1)
        tm.wr(st, b, mv, nx)
    return tag


# ---------------------------------------------------------------------------
def readgrp(tm, tag, on, entry=0):
    """head on c0 (entry 0) or c1 (entry 1); on[m] is entered on bf.

    Only the branches that can lead to one of on's markers are built, so a
    caller that can only ever see PLAIN and END pays for two leaves instead of
    eight.  A marker that cannot occur leaves its transition undefined, which
    halts the machine just as the TRAP state did."""
    S = lambda k, p: '%s#r%d_%d' % (tag, k, p)
    has = lambda k, p: any((m >> (4 - k)) == p for m in on)

    if entry == 0:
        tm.t(S(0, 0), 0, 0, 'R', S(1, 0))
        tm.t(S(0, 0), 1, 1, 'R', 'TRAP')
    for k in (1, 2, 3):
        for p in range(1 << (k - 1)):
            if not (k == 1 and p == 0) and not has(k, p):
                continue
            for b in (0, 1):
                if k < 3:
                    q = 2 * p + b
                    if has(k + 1, q):
                        tm.t(S(k, p), b, b, 'R', S(k + 1, q))
                else:
                    m = 2 * p + b
                    if m in on:
                        tm.t(S(k, p), b, b, 'R', S(4, m))
    for m in on:
        tm.t(S(4, m), 0, 0, 'R', on[m])
        tm.t(S(4, m), 1, 1, 'R', 'TRAP')
    return S(0, 0) if entry == 0 else S(1, 0)


def prevgrp(tm, tag, on):
    """from c0 to the previous group's c0, then read it."""
    tm.same('%s#p' % tag, 'L', '%s#pk' % tag)
    tm.t('%s#pk' % tag, 1, 1, 'L', '%s#pk' % tag)
    tm.t('%s#pk' % tag, 0, 0, 'L', '%s#p1' % tag)
    for i in range(1, 3):
        tm.same('%s#p%d' % (tag, i), 'L', '%s#p%d' % (tag, i + 1))
    tm.same('%s#p3' % tag, 'L', '%s#r0_0' % tag)
    readgrp(tm, tag, on)
    return '%s#p' % tag


def walkright(tm, tag, on):
    """entry '%s#r0_0' (a group's c0) or the skip state '%s#wsk' (a bf):
    read groups rightwards; on[m] is entered on bf, '%s#wsk' continues."""
    sk = '%s#wsk' % tag
    tm.t(sk, 1, 1, 'R', sk)
    tm.t(sk, 0, 0, 'R', '%s#r1_0' % tag)
    readgrp(tm, tag, on)
    return '%s#r0_0' % tag


def walkleft(tm, tag, on):
    """entry '%s#r0_0' (a group's c0) reads that group first, then steps
    left via prevgrp; on[m] is entered on bf, '%s#wsk' continues."""
    sk = '%s#wsk' % tag
    mchain(tm, sk, 5, 'L', '%s#p' % tag)
    prevgrp(tm, tag, on)
    return '%s#r0_0' % tag


def markleft(tm, tag, m, cont):
    """from bf: write marker m on the way left and keep going: the writes at
    c3, c2, c1 come in the order the leftward walk visits them, so the walk
    and the marking are one pass and `cont` is entered on the group's c0 (a
    prevgrp entry) instead of returning to the bf first."""
    tm.same('%s#0' % tag, 'L', '%s#1' % tag)        # bf -> c4
    tm.same('%s#1' % tag, 'L', '%s#2' % tag)        # -> c3
    b = BITS[m]
    tm.wr('%s#2' % tag, b[2], 'L', '%s#3' % tag)    # c3 = m0 -> c2
    tm.wr('%s#3' % tag, b[1], 'L', '%s#4' % tag)    # c2 = m1 -> c1
    tm.wr('%s#4' % tag, b[0], 'L', cont)            # c1 = m2 -> c0
    return '%s#0' % tag


def countblk(tm, tag, conts):
    """from bf: count the ones (1..6); conts[k] is entered on c1 of the
    following group."""
    tm.t('%s#0' % tag, 1, 1, 'R', '%s#1' % tag)
    tm.t('%s#0' % tag, 0, 0, 'R', 'TRAP')
    for k in range(1, 7):
        tm.t('%s#%d' % (tag, k), 1, 1, 'R',
             '%s#%d' % (tag, k + 1) if k < 6 else 'TRAP')
        tm.t('%s#%d' % (tag, k), 0, 0, 'R', conts[k])
    return '%s#0' % tag


def scan_to_b(tm, tag, hits, ks):
    """From c1 of the group after A's block, with the count k in the state.
    Between A and B every group is plain, so only B's m2 bit is 1."""
    for k in ks:
        w = '%s#%d#w' % (tag, k)
        z = '%s#%d#z' % (tag, k)
        o = '%s#%d#o' % (tag, k)
        tm.t(w, 1, 1, 'R', '%s#%d#b' % (tag, k))        # this is B
        tm.t(w, 0, 0, 'R', z)                          # plain: step over
        mchain(tm, '%s#%d#b' % (tag, k), 3, 'R', hits[k])
        # a plain group's tail is 0 0 0 1^b 0, so skipping it is two states:
        # zeros up to the block, then the block's ones up to the next c0
        tm.t(z, 0, 0, 'R', z)                           # c2, c3, c4
        tm.t(z, 1, 1, 'R', o)                           # the block
        tm.t(o, 1, 1, 'R', o)
        tm.t(o, 0, 0, 'R', w)                           # c0 -> the next c1
    return '%s#%d#w' % (tag, min(ks))


def consume(tm, tag, eq, ne0):
    """from bf of the second block, with the first block's length in the
    state: walk it consuming.  eq is entered on c1 of the group after the
    block, ne0 on c0 of a group (mismatch)."""
    tm.t('%s#sk' % tag, 1, 1, 'R', '%s#sk' % tag)
    tm.t('%s#sk' % tag, 0, 0, 'R', '%s#x' % tag)
    tm.same('%s#x' % tag, 'L', ne0)
    for k in range(6):                              # k <= 5: see above
        st = '%s#%d' % (tag, k)
        tm.t(st, 1, 1, 'R',
             '%s#%d' % (tag, k - 1) if k else '%s#sk' % tag)
        tm.t(st, 0, 0, 'R', eq if k == 0 else '%s#x' % tag)
    return '%s#6' % tag


# ---------------------------------------------------------------------------
def prune(tm, start):
    """Delete states that no run can reach (dead code left behind by the
    helpers), so the exported table only holds the live machine."""
    seen, stack = {start}, [start]
    while stack:
        q = stack.pop()
        for b in (0, 1):
            if (q, b) in tm.tr:
                nx = tm.tr[(q, b)][2]
                if nx not in seen:
                    seen.add(nx)
                    stack.append(nx)
    tm.tr = {k: v for k, v in tm.tr.items() if k[0] in seen}
    return tm


def fill_traps(tm):
    """Give every state both symbols: an impossible marker now falls through
    to halt-trap instead of leaving the transition undefined.  Costs tuples,
    no states."""
    for q in {k[0] for k in tm.tr}:
        if q in ('HALT', 'TRAP', 'STUCK'):
            continue
        for b in (0, 1):
            if (q, b) not in tm.tr:
                tm.tr[(q, b)] = (b, 'R', 'TRAP')
    return tm


def add_boot(tm, start):
    """Blank-tape bootstrap.  Nine states write the ten cells of
    start_tape() right to left; the last one leaves the head on cell 0 of
    that string -- the wall's c0 -- which is blank, so it needs no write.
    9 states, 18 tuples, and the machine then starts on empty tape."""
    s = bits_to_string(start_tape())            # ___1__111_
    names = ['BOOT%d' % i for i in range(len(s) - 1)]
    for i, st in enumerate(names):
        ch = s[len(s) - 1 - i]                  # written at position -i
        nx = names[i + 1] if i + 1 < len(names) else start
        tm.wr(st, 1 if ch == '1' else 0, 'L', nx)
    return names[0]


def compact(tm, protect=()):
    """Merge states whose transition rows are literally identical.

    Two states that write the same bit, move the same way and go to the *same*
    target for both symbols are the same state, so merging them is free.

    Anything weaker is unsound for a Turing machine: class-based (Moore)
    minimisation merges a run of identical "move right" states into one state
    with a self-loop, because a finite automaton cannot tell them apart -- but
    the machine can, since each of those states sits on a different cell.  That
    collapse silently broke the 9-state bootstrap (it ran forever on a blank
    tape), so only exact duplicates are merged here.

    Returns the state -> representative map.
    """
    total = {q: q for (q, b) in tm.tr}
    while True:
        rows = {}
        rep = {}
        for q in sorted({q for q, b in tm.tr}):
            row = tuple(tm.tr[(q, b)] for b in (0, 1))
            if row in rows:
                keep = rows[row]
                if q in protect:      # keep the name a probe looks for
                    keep = rows[row] = q
            else:
                keep = rows[row] = q
            rep[q] = keep
        if all(rep[q] == q for q in rep):
            return total
        tm.tr = {(rep[q], b): (w, mv, nx if nx is None or nx not in rep else rep[nx])
                 for (q, b), (w, mv, nx) in tm.tr.items()}
        for q in total:
            total[q] = rep.get(total[q], total[q])


def build(halt_on=5, boot=True):
    tm = TM()
    t = tm.t
    # the start tape is fixed (wall + end marker, no blocks), so the reader is
    # blind: ten rights to the end marker's bf, five back to its c0
    START = mchain(tm, 'T', 10, 'R', 'T#e')
    mchain(tm, 'T#e', 5, 'L', 'AP0')

    # a new record always starts at candidate 0
    wchain(tm, 'AP0', [0, 0, 0, 0, 0] + [1] + group(END), 'R', 'AP0#b')
    mchain(tm, 'AP0#b', 5, 'L', 'P1#p')

    # a fresh record: its pair is itself and the third from the end, so the
    # right walker goes on it straight away and only two anchors plus the left
    # walker's record have to be marked
    prevgrp(tm, 'P1', {PLAIN: 'P1w#0', WALL: 'NOPE#bf'})
    markleft(tm, 'P1w', W, 'P2#p')                 # right walker: new record
    prevgrp(tm, 'P2', {PLAIN: 'P2m#0', W: 'P2m#0', WALL: 'NOPE#bf'})
    markleft(tm, 'P2m', B, 'P3#p')                 # B one record left
    # the third-from-end record is round one's left walker, and P3w marks it W
    # on the way left -- a separate A first would be overwritten in place
    prevgrp(tm, 'P3', {PLAIN: 'P3w#0', W: 'P3w#0', WALL: 'NOPE#bf'})

    # one loop: the anchors are the next round's walkers, so the walkers always
    # sit exactly on the pair (A_m, B_m) and the t = 0 comparison is just the
    # first trip through this same scan/consume/advance code
    countblk(tm, 'CW', {k: 'SW#%d#w' % k if k < 6 else 'TRAP'
                        for k in range(1, 7)})
    scan_to_b(tm, 'SW', {k: 'Y#%d' % k for k in range(1, 6)}, range(1, 6))
    consume(tm, 'Y', 'E1#r1_0', 'FA#r0_0')
    readgrp(tm, 'E1', {END: 'FBm3#0', PLAIN: 'ADV#wsk'}, entry=1)

    # advance both walkers one record right: every W met on the way left is
    # moved one record right, then a short walk right finds the left walker
    # same trick as FA: read each group while walking left, so c3 = m0,
    # c2 = m1, c1 = m2 arrive in order and readgrp/prevgrp are not needed
    tm.same('ADV#wsk', 'L', 'ADV#t4')              # entry: bf -> c4
    tm.same('ADV#t4', 'L', 'ADV#t3')               # c4 -> c3 = m0
    tm.t('ADV#t3', 1, 1, 'L', 'ADV#z1')            # 1: the wall or an end marker
    tm.t('ADV#t3', 0, 0, 'L', 'ADV#z0')            # 0: a record
    tm.t('ADV#z1', 0, 0, 'R', 'ADV#w1')            # 001 is the wall: turn round
    tm.t('ADV#z1', 1, 1, 'L', 'ADV#c1')            # 011/111: walk on
    tm.same('ADV#w1', 'R', 'ADV#w2')               # wall c3 -> c4
    tm.same('ADV#w2', 'R', 'ADVW#r0_0')            # -> its bf, then rightwards
    tm.t('ADV#z0', 0, 0, 'L', 'ADV#c1')            # m1 = 0: A (100) or plain
    tm.t('ADV#z0', 1, 1, 'L', 'ADV#b')             # m1 = 1: B (010) or W (110)
    tm.t('ADV#b', 0, 0, 'L', 'ADV#r0_0')           # m2 = 0: B, walk on
    tm.t('ADV#b', 1, 0, 'R', 'ADVm#0')             # m2 = 1: W, slide it right
    tm.same('ADV#c1', 'L', 'ADV#r0_0')             # c1 -> c0
    tm.same('ADV#r0_0', 'L', 'ADV#sk')             # c0 -> the previous block
    tm.t('ADV#sk', 1, 1, 'L', 'ADV#sk')            # over the block
    tm.t('ADV#sk', 0, 0, 'L', 'ADV#t3')            # -> the next group's c3
    # slide one W one record right: m1/m2 blanked here and rewritten on the
    # group after the block, all in one left-to-right pass
    tm.wr('ADVm#0', 0, 'R', 'ADVm#1')              # c2 = m1 -> 0
    tm.t('ADVm#1', 0, 0, 'R', 'ADVm#1')            # over the blanked tail
    tm.t('ADVm#1', 1, 1, 'R', 'ADVm#2')            # up to the block
    tm.t('ADVm#2', 1, 1, 'R', 'ADVm#2')            # over the block
    tm.t('ADVm#2', 0, 0, 'R', 'ADVm#3')            # next group's c0 -> c1
    tm.wr('ADVm#3', 1, 'R', 'ADVm#4')              # m2 = 1
    tm.wr('ADVm#4', 1, 'L', 'ADVm#5')              # m1 = 1
    tm.same('ADVm#5', 'L', 'ADV#r0_0')             # c1 -> c0, walk on left
    walkright(tm, 'ADVW', {W: 'CW#0', PLAIN: 'ADVW#wsk', A: 'ADVW#wsk',
                           B: 'ADVW#wsk'})

    # next round: the anchors become the walkers and move on.  From a mismatch
    # one leftward pass does all of it -- B becomes the right walker with the
    # new B one record left, the stale walkers are dropped, A becomes the left
    # walker with the new A two records left -- and it ends on the left walker.
    # The mismatch walk reads every group it passes while walking left, so the
    # marker bits arrive as c3 = m0, c2 = m1, c1 = m2 -- the order they are
    # needed in.  That replaces readgrp's tree, its 5-left skip and prevgrp's
    # 5 states with a hard-wired test, and the marker rewrites happen in the
    # same pass: all four record markers have m0 = 0, so only m1/m2 move.
    tm.same('FA#r0_0', 'L', 'FA#sk')               # step over the entry group
    tm.t('FA#sk', 1, 1, 'L', 'FA#sk')              # ... and its block
    tm.t('FA#sk', 0, 0, 'L', 'FA#t3')              # -> the group's c3 = m0
    tm.t('FA#t3', 1, 1, 'L', 'FA#z1')              # 1: the wall or an end marker
    tm.t('FA#t3', 0, 0, 'L', 'FA#z0')              # 0: a record
    tm.t('FA#z1', 0, 0, 'R', 'VT#t')               # 001 is the wall: no m, legal
    tm.t('FA#z1', 1, 1, 'L', 'FA#c1')              # 011/111: keep walking
    tm.t('FA#z0', 0, 0, 'L', 'FA#a')               # m1 = 0: A (100) or plain
    tm.t('FA#z0', 1, 1, 'L', 'FA#b')               # m1 = 1: B (010) or W (110)
    tm.t('FA#a', 1, 1, 'R', 'FA#sa')               # m2 = 1: A -> W (m1 = 1)
    tm.t('FA#a', 0, 0, 'L', 'FA#r0_0')             # plain: nothing to change
    tm.t('FA#b', 0, 1, 'R', 'FA#sb')               # m2 = 0: B -> W (m2 = 1)
    tm.t('FA#b', 1, 0, 'R', 'FA#sw')               # m2 = 1: stale W -> plain
    tm.same('FA#c1', 'L', 'FA#r0_0')               # c1 -> c0, carry on left
    tm.wr('FA#sa', 1, 'L', 'FA#sa1')               # m1 = 1
    tm.same('FA#sa1', 'L', 'FC#p')                 # A becomes the left walker
    tm.wr('FA#sb', 1, 'L', 'FA#sb1')               # m1 = 1 (B already has it)
    tm.same('FA#sb1', 'L', 'FB#p')                 # B becomes the right walker
    tm.wr('FA#sw', 0, 'L', 'FA#c1')                # m1 = 0
    prevgrp(tm, 'FB', {PLAIN: 'FBm#0', A: 'FBm#0', W: 'FBm#0',
                       WALL: 'NOPE#bf'})
    markleft(tm, 'FBm', B, 'FA#r0_0')              # new B, one record left
    markleft(tm, 'P3w', W, 'FC#p')                 # round one: A -> left walker
    prevgrp(tm, 'FC', {PLAIN: 'FC1#s', W: 'FC1#s', WALL: 'WY#wsk'})
    mchain(tm, 'FC1#s', 5, 'L', 'FC2#p')
    prevgrp(tm, 'FC2', {PLAIN: 'FCm#0', W: 'FCm#0', WALL: 'WY#wsk'})
    markleft(tm, 'FCm', A, 'WY#r0_0')              # new A, two records left
    # the left walker is two records right of the new A: if the new A does not
    # exist this round still runs (WY#wsk), and with no A left the next mismatch
    # walk hits the wall -- legal
    walkright(tm, 'WY', {W: 'CW#0', PLAIN: 'WY#wsk', A: 'WY#wsk',
                         B: 'WY#wsk'})

    # verdicts: one shared path.  The verdict rides in the end marker -- 7 for
    # legal (no m matched, the search ran off the wall) and 3 for illegal (a
    # match reached the last record) -- so walk, sweep and dispatch exist once.
    markleft(tm, 'FBm3', 3, 'V#s')                 # FORBID: on the end bf
    tm.same('V#s', 'L', 'VT')                      # end c0 -> last block's end
    # walk left to the wall: it is the only group whose low marker bit is 1
    # (both end markers skip this route, so 3 cannot be confused with it)
    tm.t('VT', 1, 1, 'L', 'VT')                    # skip the block leftwards
    tm.t('VT', 0, 0, 'L', 'VT#t')                  # c4 -> c3 = m0
    tm.t('VT#t', 1, 1, 'R', 'VT#w')                # m0 = 1: the wall, turn round
    tm.t('VT#t', 0, 0, 'L', 'VT#b1')               # a record: step over it
    tm.same('VT#b1', 'L', 'VT#b2')                 # c2
    tm.same('VT#b2', 'L', 'VT#b3')                 # c1
    tm.same('VT#b3', 'L', 'VT')                    # c0 -> previous block's end
    tm.same('VT#w', 'R', 'VT#w1')                  # wall m1 -> c4
    tm.same('VT#w1', 'R', 'V#w#1')                 # wall bf -> first record's c1
    mchain(tm, 'NOPE#bf', 2, 'L', 'VT#t')          # NOPE: on the wall's c4 -> m0
    sweep(tm, 'V#w', 'V#e')
    mchain(tm, 'V#e', 5, 'L', 'Hp#p')              # end bf -> end c0 -> count
    dispatch(tm, halt_on)
    tm.wr('AP0x', 0, 'R', 'AP0#1')
    rewrite(tm, 'UP')
    if boot:
        START = add_boot(tm, START)
    prune(tm, START)
    fill_traps(tm)
    rep = compact(tm, protect=('AP0x',))
    for q in list(rep):                 # re-point anything merged after the fact
        rep[q] = rep.get(rep[q], rep[q])
    START = rep[START]
    return tm, START


def sweep(tm, tag, done):
    """From the first record's c1: walk right blanking every marker and stop
    on the end marker's bf.  The wall is the one group that keeps its marker.
    No group read is needed: blocks are never empty and both end markers have
    m0 = 1 (7 legal, 3 illegal), while every record marker (0, A, B, W) has
    m0 = 0 -- so that single bit says whether the group is the end."""
    tm.same('%s#1' % tag, 'R', '%s#2' % tag)        # c1 -> c2
    tm.same('%s#2' % tag, 'R', '%s#3' % tag)        # -> c3
    tm.t('%s#3' % tag, 1, 1, 'R', '%s#4' % tag)     # m0 = 1: the end marker
    tm.t('%s#3' % tag, 0, 0, 'L', '%s#5' % tag)     # a record: blank it
    tm.same('%s#4' % tag, 'R', done)                # c4 -> the end marker's bf
    tm.wr('%s#5' % tag, 0, 'L', '%s#6' % tag)       # c2 = m1 -> 0
    tm.wr('%s#6' % tag, 0, 'R', '%s#7' % tag)       # c1 = m2 -> 0
    tm.t('%s#7' % tag, 0, 0, 'R', '%s#7' % tag)     # over the blanked tail
    tm.t('%s#7' % tag, 1, 1, 'R', '%s#8' % tag)     # up to the block
    tm.t('%s#8' % tag, 1, 1, 'R', '%s#8' % tag)     # over the block
    tm.t('%s#8' % tag, 0, 0, 'R', '%s#1' % tag)     # the next record's c1
    return '%s#1' % tag


def dispatch(tm, halt_on):
    """From the end marker's c0: read the last record's block back and act.
    countblk stops on the end marker's c1, which is its top marker bit, so the
    verdict (7 legal / 3 illegal) is read for free at the moment the length is
    known -- one read-back serves both verdicts."""
    prevgrp(tm, 'Hp', {PLAIN: 'Hc#0', WALL: 'TRAP'})
    countblk(tm, 'Hc', {k: 'H#%d' % k for k in range(1, 7)})
    for k in range(1, 7):
        v = k - 1
        tm.t('H#%d' % k, 1, 1, 'L', 'HALT' if v == halt_on else 'AP0x')
        tm.t('H#%d' % k, 0, 0, 'L', 'STUCK' if v == 5 else 'UP#0')


def rewrite(tm, tag):
    """From the end marker's c0: the next candidate is the failed one plus
    one, so its block is the current block plus a single 1 and the end marker
    just slides one cell right.  No per-value code is needed."""
    tm.wr(tag + '#0', 1, 'R', tag + '#1')                 # block grows by one
    wchain(tm, tag + '#1', group(END), 'R', tag + '#e')   # end marker, shifted
    mchain(tm, tag + '#e', 5, 'L', 'P1#p')                # -> CHK


# ---------------------------------------------------------------------------
def export_morphett(tm, start, path):
    halt_label = {'HALT': 'halt', 'TRAP': 'halt-trap', 'STUCK': 'halt-stuck'}
    ids, order = {}, []

    def sid(q):
        if q not in ids:
            ids[q] = halt_label.get(q, str(len(order)))
            order.append(q)
        return ids[q]

    sid(start)
    for (q, b) in sorted(tm.tr):
        sid(q)
        sid(tm.tr[(q, b)][2])
    lines = ['; greedy U.a.U-avoiding sequence on 2 symbols {1, _} (blank = _)',
             '; start state 0; "halt" is reached iff a 5 was placed',
             '; tape: groups 0 m2 m1 m0 0, records = group + 1^(v+1)',
             '; markers: 0 plain, 1 wall, 2 B, 4 A, 6 W, 7 end, 3 end(illegal)',
             ';',
             '; initial tape: blank.  States BOOT0..BOOT8 write',
             ';   ' + bits_to_string(start_tape()) + '  (right to left, 9 states)',
             '; and leave the head on the wall c0; state 0 is the bootstrap.', '']
    for (q, b) in sorted(tm.tr):
        w, mv, nx = tm.tr[(q, b)]
        lines.append('%s %s %s %s %s' % (ids[q], '1' if b else '_',
                                         '1' if w else '_', mv.lower(),
                                         ids[nx]))
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    return len(order), len(tm.tr), ids[start]


def bits_to_string(bits):
    return ''.join('1' if b else '_' for b in bits)


def parse(tape):
    if not tape:
        return []
    lo, hi = min(tape), max(tape)
    cells = [tape.get(i, 0) for i in range(lo, hi + 1)]
    w = group(WALL)
    i = 0
    while cells[i:i + 5] != w:
        i += 1
        if i > len(cells):
            raise ValueError('no wall')
    i += 5
    seq = []
    while True:
        g = cells[i:i + 5]
        if g == group(END):
            return seq
        if len(g) < 5 or g[0] or g[4]:
            raise ValueError('bad group %r at %d' % (g, i))
        i += 5
        n = 0
        while i < len(cells) and cells[i] == 1:
            n += 1
            i += 1
        if n == 0:
            raise ValueError('empty block at %d' % i)
        seq.append(n - 1)


def run(tm, start, steps, probe=('AP0x',), blank=False):
    tape = {} if blank else dict(enumerate(start_tape()))
    pos, st, n, seen = 0, start, 0, []
    while n < steps:
        b = tape.get(pos, 0)
        if (st, b) not in tm.tr:
            return 'halt', st, n, tape, pos, seen
        w, mv, nx = tm.tr[(st, b)]
        tape[pos] = w
        pos += 1 if mv == 'R' else -1
        st = nx
        n += 1
        if st in probe:
            seen.append((n, parse(tape)))
    return 'limit', st, n, tape, pos, seen


def main():
    ref = reference(400)                            # the 2M run emits < 100
    print('reference:', ref[:12])
    ok = True
    for halt_on in (0, 1, 2, 3):
        tm, start = build(halt_on)
        want = ref[:ref.index(halt_on) + 1]
        res, st, n, tape, pos, seen = run(tm, start, 20_000_000, blank=True)
        try:
            got = parse(tape)
        except ValueError as e:
            got = 'parse error: %s' % e
        good = res == 'halt' and got == want
        ok &= good
        print('halt_on %d: %-5s steps=%-9d %s   %s'
              % (halt_on, res, n, got, 'OK' if good else 'want %s' % want))
    tm5, start5 = build(5)
    states = {q for (q, b) in tm5.tr}
    holes = [(q, b) for q in states for b in (0, 1)
             if (q, b) not in tm5.tr and q not in ('HALT', 'TRAP', 'STUCK')]
    print('machine: %d states, %d tuples, %d holes'
          % (len(states), len(tm5.tr), len(holes)))
    ok &= not holes
    budget = 2_000_000
    res, st, n, tape, pos, seen = run(tm5, start5, budget, blank=True)
    got = seen[-1][1] if seen else []
    print('halt_on 5: %-5s after %d steps, %d symbols' % (res, n, len(got)))
    print('  emitted:', got)
    # a shorter run must not pass this by emitting nothing: require a real prefix
    enough = len(got) >= 80
    print('  prefix ok:', got == ref[:len(got)] and enough,
          '(emitted %d, need >= 80)' % len(got))
    ok &= got == ref[:len(got)] and enough and res != 'halt'
    states5 = {q for (q, b) in tm5.tr}
    dangling = {t[2] for t in tm5.tr.values()} - states5 - {'HALT', 'TRAP', 'STUCK'}
    print('undefined jump targets:', dangling or 'none')
    ok &= not dangling
    ns, nt, sid = export_morphett(tm5, start5, 'uubin.tm')
    print('wrote uubin.tm: %d states, %d tuples, start %s' % (ns, nt, sid))
    print('start: blank tape (bootstrap writes %s, head ends on its c0)'
          % bits_to_string(start_tape()))
    print('ALL CHECKS PASSED' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
