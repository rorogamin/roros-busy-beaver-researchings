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


def setmark(tm, tag, m, cont):
    """from bf: write marker m; back on bf afterwards."""
    for i in range(4):                              # bf -> c4,c3,c2,c1
        tm.same('%s#%d' % (tag, i), 'L', '%s#%d' % (tag, i + 1))
    b = BITS[m]
    tm.wr('%s#4' % tag, b[0], 'R', '%s#5' % tag)    # c2
    tm.wr('%s#5' % tag, b[1], 'R', '%s#6' % tag)    # c3
    tm.wr('%s#6' % tag, b[2], 'R', '%s#7' % tag)    # c4
    tm.same('%s#7' % tag, 'R', cont)                # bf
    return '%s#0' % tag


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


def advwalk(tm, tag, cont):
    """from a walker's bf: slide its marker one record right.  Left over its
    own group blanking m1/m2, then right across the block writing m1/m2 on the
    group after it.  `cont` is entered on that group's c0 (a prevgrp entry)."""
    tm.same('%s#0' % tag, 'L', '%s#1' % tag)        # bf -> c4
    tm.same('%s#1' % tag, 'L', '%s#2' % tag)        # -> c3 (m0, see W)
    tm.same('%s#2' % tag, 'L', '%s#3' % tag)        # -> c2
    tm.wr('%s#3' % tag, 0, 'L', '%s#4' % tag)       # blank m1 -> c1
    tm.wr('%s#4' % tag, 0, 'R', '%s#5' % tag)       # blank m2, turn back
    tm.t('%s#5' % tag, 0, 0, 'R', '%s#5' % tag)     # over the blanked tail
    tm.t('%s#5' % tag, 1, 1, 'R', '%s#6' % tag)     # to the block
    tm.t('%s#6' % tag, 1, 1, 'R', '%s#6' % tag)     # over the block
    tm.t('%s#6' % tag, 0, 0, 'R', '%s#7' % tag)     # next group's c0 -> c1
    tm.wr('%s#7' % tag, 1, 'R', '%s#8' % tag)       # m2 = 1
    tm.wr('%s#8' % tag, 1, 'L', '%s#9' % tag)       # m1 = 1
    tm.same('%s#9' % tag, 'L', cont)                # c1 -> c0
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
    prevgrp(tm, 'P3', {PLAIN: 'P3m#0', W: 'P3m#0', WALL: 'NOPE#bf'})
    setmark(tm, 'P3m', A, 'FAa#0')                 # A two records left

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
    walkleft(tm, 'ADV', {W: 'ADVm#0', PLAIN: 'ADV#wsk', A: 'ADV#wsk',
                         B: 'ADV#wsk', WALL: 'ADVW#wsk', END: 'ADV#wsk'})
    advwalk(tm, 'ADVm', 'ADV#p')                   # each W one record right
    walkright(tm, 'ADVW', {W: 'CW#0', PLAIN: 'ADVW#wsk', A: 'ADVW#wsk',
                           B: 'ADVW#wsk'})

    # next round: the anchors become the walkers and move on.  From a mismatch
    # one leftward pass does all of it -- B becomes the right walker with the
    # new B one record left, the stale walkers are dropped, A becomes the left
    # walker with the new A two records left -- and it ends on the left walker.
    walkleft(tm, 'FA', {B: 'FAb#0', A: 'FAa#0', W: 'FAw#0', PLAIN: 'FA#wsk',
                        WALL: 'NOPE#bf', END: 'FA#wsk', ILLEGAL: 'FA#wsk'})
    markleft(tm, 'FAw', PLAIN, 'FA#p')             # drop a stale walker
    markleft(tm, 'FAb', W, 'FB#p')                 # B -> right walker
    prevgrp(tm, 'FB', {PLAIN: 'FBm#0', A: 'FBm#0', W: 'FBm#0',
                       WALL: 'NOPE#bf'})
    markleft(tm, 'FBm', B, 'FA#p')                 # new B, one record left
    markleft(tm, 'FAa', W, 'FC#p')                 # A -> left walker
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
    tm.t('VT#t', 1, 1, 'L', 'VT#w')                # m0 = 1: the wall
    tm.t('VT#t', 0, 0, 'L', 'VT#b1')               # a record: step over it
    tm.same('VT#b1', 'L', 'VT#b2')                 # c2
    tm.same('VT#b2', 'L', 'VT#b3')                 # c1
    tm.same('VT#b3', 'L', 'VT')                    # c0 -> previous block's end
    tm.same('VT#w', 'L', 'VT#w1')                  # wall m1 -> m2
    tm.same('VT#w1', 'L', 'V#w#r0_0')              # -> the wall's c0
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
    return tm, START


def sweep(tm, tag, done):
    """from the wall's c0: walk right to the end marker, clearing markers;
    `done` is entered on the end marker's bf."""
    walkright(tm, tag, {END: done, 3: done, PLAIN: '%s#cm#0' % tag,
                        A: '%s#cm#0' % tag, B: '%s#cm#0' % tag,
                        W: '%s#cm#0' % tag, WALL: '%s#wsk' % tag})
    setmark(tm, '%s#cm' % tag, PLAIN, '%s#wsk' % tag)


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
    ref = reference(80)
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
    print('  prefix ok:', got == ref[:len(got)])
    ok &= got == ref[:len(got)] and res != 'halt'
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
