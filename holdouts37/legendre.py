"""A Turing machine that halts iff Legendre's conjecture is false.

Legendre: for every n >= 1 there is a prime p with n*n < p < (n+1)*(n+1).

Cell i of the tape is the number i.  One pass over the line marks every k-th
cell composite; passes run k = 2, 3, 4, ... until one of them marks nothing --
at that point 2k > length, so every composite on the line has a factor <= half
the length and the line is fully sieved.  Then the machine walks the intervals:
from n*n+1 it steps 2n cells, which lands exactly on (n+1)*(n+1); if no live
cell turned up in between it halts.  Running off the end of the line grows it
and sieving starts over.  Nothing is ever unmarked.

Tape:   ^  +++  |  ccc....  (  F  )  1 1 2 1 1 ...  ]
        wall stride  wall countdown walls flag   the number line   end

Symbols: '_' blank, '^' '|' '(' ')' ']' walls, '+' stride cell, 'c' countdown
cell, 'F' flag, '1' live, '2' composite, 'L'/'M' cursor marks, '=' spent stride cell.
('#' and ';' would start comments in Morphett format, so '+' is the stride cell.)
"""

BL = '_'
LW, SW, CW, FW, RW = '^', '|', '(', ')', ']'
K, D, FL = '+', 'c', 'F'
LIVE, COMP, ML, MM, MK = '1', '2', 'L', 'M', '='
SYMS = [BL, LW, SW, CW, FW, RW, K, D, FL, LIVE, COMP, ML, MM, MK]
PASS = [BL, SW, CW, FL, FW, D, MK, K, LIVE, COMP]

R = []
_seen = {}


def rule(a, b, c, d, e):
    key = (a, b)
    assert key not in _seen, 'duplicate rule for %s on %s' % (a, b)
    _seen[key] = True
    R.append('%s %s %s %s %s' % (a, b, c, d, e))


def home(st, then):
    for s in SYMS:
        if s != LW:
            rule(st, s, s, 'l', st)
    rule(st, LW, LW, '*', then)


def fill(prefix, per_cell, tail):
    """copy the stride block into C, `per_cell` countdown cells per stride cell

    Countdown cells are written against the right wall of their region, so the
    number to eat is always the cell just left of '(' -- no scanning needed."""
    p = prefix
    rule(p + '0', LW, LW, 'r', p + ('h' if per_cell == 'half' else '1'))
    rule(p + '1', LW, LW, 'r', p + '1')
    rule(p + '1', MK, MK, 'r', p + '1')
    rule(p + '1', BL, BL, 'r', p + '1')
    rule(p + '1', K, MK, 'r', p + '2')
    if per_cell == 'half':
        rule(p + 'h', BL, BL, 'r', p + 'h')
        rule(p + 'h', K, MK, 'r', p + '1')      # this stride cell is already counted
        rule(p + 'h', SW, SW, 'l', p + '9')
    rule(p + '1', SW, SW, 'l', p + '9')
    for s_ in [MK, SW, D, K, BL]:
        rule(p + '2', s_, s_, 'r', p + '2')
    rule(p + '2', CW, CW, 'l', p + '3')
    rule(p + '3', D, D, 'l', p + '3')
    if per_cell == 2:
        rule(p + '3', BL, D, 'l', p + '4')
        rule(p + '4', BL, D, 'l', p + '5')
        rule(p + '4', SW, SW, 'l', p + '5')
    else:
        rule(p + '3', BL, D, 'l', p + '5')
    rule(p + '3', SW, SW, 'l', p + '5')
    rule(p + '5', D, D, 'l', p + '5')
    rule(p + '5', SW, SW, 'l', p + '5')
    rule(p + '5', BL, BL, 'l', p + '5')
    rule(p + '5', MK, MK, 'l', p + '5')
    rule(p + '5', K, K, 'l', p + '5')
    rule(p + '5', LW, LW, '*', p + ('1' if per_cell == 'half' else '0'))
    for s_ in SYMS:
        if s_ != LW:
            rule(p + '9', s_, s_, 'l', p + '9')
    rule(p + '9', LW, LW, '*', p + '91')
    rule(p + '91', LW, LW, 'r', p + '92')
    rule(p + '92', K, K, 'r', p + '92')
    rule(p + '92', BL, BL, 'r', p + '92')
    rule(p + '92', MK, K, 'r', p + '92')
    rule(p + '92', SW, SW, 'r', tail)


def shift1(p):
    """shift the wall bed from '(' to ']' one place right.

    Exits on the blank left behind by '(', with the countdown one cell wider."""
    for s_ in SYMS:
        if s_ != RW:
            rule(p + '0', s_, s_, 'r', p + '0')
    rule(p + '0', RW, BL, 'r', p + '1')      # blank the old end
    rule(p + '1', BL, RW, 'l', p + '2')      # new end, one to the right
    rule(p + '2', BL, BL, 'l', p + '3')      # the last real cell
    for i, s_ in enumerate(SYMS):
        if s_ == CW:
            continue
        rule(p + '3', s_, BL, 'r', p + 't%d' % i)
        rule(p + 't%d' % i, BL, s_, 'l', p + 'u%d' % i)
        rule(p + 'u%d' % i, BL, BL, 'l', p + '3')
    rule(p + '3', CW, BL, 'r', p + 'v')      # '(' is shifted last
    rule(p + 'v', BL, CW, 'l', p + 'w')
    rule(p + 'w', BL, BL, 'l', p + '9')


def increment(p, then):
    """one more stride cell: widen the countdown by two, add the stride cell"""
    rule(p + '0', BL, BL, 'r', p + '0')
    rule(p + '0', MK, MK, 'r', p + '0')
    rule(p + '0', K, K, 'r', p + '0')
    rule(p + '0', SW, SW, 'r', p + 'k10')
    rule(p + '0', CW, CW, '*', p + 'k10')
    shift1(p + 'k1')
    rule(p + 'k19', BL, BL, 'r', p + 'r1')
    rule(p + 'r1', BL, BL, 'r', p + 'r1')
    rule(p + 'r1', CW, CW, '*', p + 'k20')
    shift1(p + 'k2')
    rule(p + 'k29', BL, BL, 'r', p + 'r2')
    rule(p + 'r2', BL, BL, 'r', p + 'r2')
    rule(p + 'r2', CW, CW, '*', p + 'k30')
    shift1(p + 'k3')
    rule(p + 'k39', BL, BL, 'l', p + 'g')
    rule(p + 'g', BL, BL, 'l', p + 'g')
    rule(p + 'g', K, K, 'l', p + 'g')
    rule(p + 'g', MK, MK, 'l', p + 'g')
    rule(p + 'g', SW, K, 'r', p + 'g2')       # the stride cell takes the wall's place
    rule(p + 'g2', BL, SW, '*', then)          # and the wall moves into the new gap
    rule(p + 'g2', K, SW, '*', then)



# ------------------------------------------------------------------- boot
rule('0', BL, BL, 'r', '0')           # walk in to the left wall
rule('0', LW, LW, 'r', 'r1')
rule('r1', LW, LW, 'r', 'r1')
rule('r1', BL, BL, 'r', 'r1')           # skip gaps left of the stride block
rule('r1', MK, MK, 'r', 'r2')
rule('r1', K, K, 'r', 'r2')             # keep this cell
rule('r2', MK, MK, 'r', 'r3')
rule('r2', K, K, 'r', 'r3')             # keep a second
rule('r2', BL, K, 'r', 'r3')            # only one was there: add a second
rule('r3', K, BL, 'r', 'r3b')           # drop any extra stride cells
rule('r3', MK, BL, 'r', 'r3b')
rule('r3', BL, BL, 'r', 'r3')
rule('r3', SW, SW, 'r', 'r6')
rule('r3b', K, BL, 'r', 'r3b')
rule('r3b', MK, BL, 'r', 'r3b')
rule('r3b', BL, BL, 'r', 'r3b')
rule('r3b', SW, SW, 'r', 'r6')
rule('r6', D, BL, 'r', 'r6')
rule('r6', BL, BL, 'r', 'r6')
rule('r6', CW, CW, 'r', 'r7')
rule('r7', FL, BL, 'r', 'r8')           # clear the flag
rule('r7', BL, BL, 'r', 'r8')
rule('r8', FW, FW, 'l', 'r9')
home('r9', 'fs0')
fill('fs', 2, 'v0')                     # prefill 2k, then sieve

# ------------------------------------------------------------- sieve walk
for s in [K, MK, SW, D, BL, CW, FL, FW]:
    rule('v0', s, s, 'r', 'v0')
for s in [LIVE, COMP, ML, MM, RW]:
    rule('v0', s, s, '*', 'v1')
rule('v1', RW, RW, 'l', 'e0')           # end of the line
rule('v1', LIVE, ML, 'l', 'w1')
rule('v1', COMP, MM, 'l', 'w1')
for s in [LIVE, COMP]:
    rule('w1', s, s, 'l', 'w1')
rule('w1', FW, FW, 'l', 'w1')
rule('w1', FL, FL, 'l', 'w2')
rule('w1', BL, BL, 'l', 'w2')
rule('w2', CW, CW, 'l', 'w2b')
rule('w2b', D, D, 'l', 'w3')            # the countdown has cells left
rule('w2b', BL, BL, 'r', 'wc0')
rule('w2b', SW, SW, 'r', 'wc0')         # countdown empty: a multiple of k
rule('w3', D, D, 'l', 'w3')             # walk left along the countdown
rule('w3', SW, SW, 'r', 'w3d')          # block reaches the wall
rule('w3', BL, BL, 'r', 'w3d')          # the blank just left of the block
rule('w3d', D, BL, 'r', 'w4')           # eat the leftmost cell, keep the rest flush
for s in [D, BL, CW, FL, FW, LIVE, COMP]:
    rule('w4', s, s, 'r', 'w4')
rule('w4', ML, LIVE, 'r', 'v1')
rule('w4', MM, COMP, 'r', 'v1')
# countdown empty: set the flag, refill with k, then mark this cell composite
rule('wc0', CW, CW, 'r', 'wc1')         # step onto the flag
rule('wc1', BL, FL, 'l', 'wc2')         # set it
rule('wc1', FL, FL, 'l', 'wc2')
rule('wc2', CW, CW, 'l', 'wc4')         # back to the wall
home('wc4', 'g0')
fill('g', 'half', 'g93')                     # refill k countdown cells
for s in PASS:
    rule('g93', s, s, 'r', 'g93')
rule('g93', ML, COMP, 'r', 'v1')
rule('g93', MM, COMP, 'r', 'v1')

# ------------------------------------------------------------- pass over
for s in [LIVE, COMP]:
    rule('e0', s, s, 'l', 'e0')
rule('e0', FW, FW, 'l', 'e0')
rule('e0', FL, FL, '*', 'e1')           # something got marked
rule('e0', BL, BL, '*', 'e2')           # nothing got marked: sieving is done
rule('e1', FL, BL, 'l', 'e1b')          # clear the flag
rule('e1b', CW, CW, 'l', 'e1c')         # onto the countdown
rule('e1c', D, BL, 'l', 'e1c')
rule('e1c', K, K, 'l', 'e1c')
rule('e1c', MK, MK, 'l', 'e1c')          # empty it
rule('e1c', BL, BL, 'l', 'e1c')
rule('e1c', SW, SW, 'r', 'e1d')
rule('e1d', BL, BL, 'r', 'e1d')
rule('e1d', K, K, 'r', 'e1d')
rule('e1d', MK, MK, 'r', 'e1d')
rule('e1d', CW, CW, 'r', 'e1e')
home('e1e', 'e3')
rule('e3', LW, LW, 'r', 'e3a')
rule('e3a', K, K, 'r', 'e3a')
rule('e3a', BL, BL, 'r', 'e3a')
rule('e3a', SW, SW, '*', 'iz0')          # k += 1, countdown grows with it
increment('iz', 'e3c')
rule('e3c', SW, SW, 'r', 'e3c')
rule('e3c', K, K, 'r', 'e3c')
rule('e3c', MK, MK, 'r', 'e3c')
rule('e3c', D, BL, 'r', 'e3c')
rule('e3c', BL, BL, 'r', 'e3c')
rule('e3c', CW, CW, 'r', 'e3d')
rule('e3d', FL, BL, 'l', 'e3e')
rule('e3d', BL, BL, 'l', 'e3e')
home('e3e', 'fs1')
# sieving finished: S := 1 cell, then the check phase
rule('e2', BL, BL, 'l', 'e2a')
rule('e2a', CW, CW, 'l', 'e2b')
home('e2b', 'e2c')
rule('e2c', LW, LW, 'r', 'e2d')
rule('e2d', K, K, 'r', 'e2e')
rule('e2e', BL, BL, 'r', 'e2e')
rule('e2e', K, BL, 'r', 'e2e')
rule('e2e', MK, BL, 'r', 'e2e')
rule('e2e', SW, SW, 'r', 'e2f')
rule('e2f', D, BL, 'r', 'e2f')
rule('e2f', BL, BL, 'r', 'e2f')
rule('e2f', CW, CW, 'r', 'e2g')
rule('e2g', FL, BL, 'l', 'e2h')
rule('e2g', BL, BL, 'l', 'e2h')
home('e2h', 'fc0')
fill('fc', 2, 'qc0')                    # C = 2*1, then start the check

# ------------------------------------------------------------- check walk
for s in [K, MK, SW, D, BL, CW, FL, FW]:
    rule('qc0', s, s, 'r', 'qc0')
rule('qc0', COMP, COMP, 'r', 'qc1')     # cells 0 and 1 are not primes
rule('qc1', COMP, COMP, 'r', 'q1')
rule('q1', RW, RW, 'l', 'x6')           # ran off the end
rule('q1', LIVE, ML, 'l', 'q2')
rule('q1', COMP, MM, 'l', 'q3')
for s in [LIVE, COMP]:
    rule('q2', s, s, 'l', 'q2')
rule('q2', FW, FW, 'l', 'q2')
rule('q2', FL, FL, 'l', 'q2a')
rule('q2', BL, FL, 'l', 'q2a')
rule('q2a', CW, CW, 'l', 'q4')
for s in [LIVE, COMP]:
    rule('q3', s, s, 'l', 'q3')
rule('q3', FW, FW, 'l', 'q3')
rule('q3', FL, FL, 'l', 'q3a')
rule('q3', BL, BL, 'l', 'q3a')
rule('q3a', CW, CW, 'l', 'q4')
rule('q4', D, D, 'l', 'q4')
rule('q4', K, K, 'l', 'q4')
rule('q4', MK, MK, 'l', 'q4')            # walk to the left edge of the countdown
rule('q4', BL, BL, 'r', 'q4b')
rule('q4', SW, SW, 'r', 'q4b')
rule('q4b', D, BL, 'r', 'q4c')          # eat the leftmost cell
rule('q4c', BL, BL, 'r', 'q4c')
rule('q4c', K, K, 'r', 'q4c')
rule('q4c', MK, MK, 'r', 'q4c')
rule('q4c', D, D, 'r', 'q4c')
rule('q4c', CW, CW, 'l', 'q5')
rule('q5', D, D, 'r', 'q5b')            # cells remain: keep checking
rule('q5', BL, BL, 'r', 'qb0')          # interval exhausted: boundary
rule('q5b', D, D, 'r', 'q5b')
rule('q5b', BL, BL, 'r', 'q5b')
rule('q5b', CW, CW, 'r', 'q6')
for s in [D, BL, CW, FL, FW, LIVE, COMP]:
    rule('q6', s, s, 'r', 'q6')
rule('q6', ML, LIVE, 'r', 'q1')
rule('q6', MM, COMP, 'r', 'q1')
# boundary (n+1)^2: was anything live in the interval?
rule('qb0', CW, CW, 'r', 'qb1')
rule('qb1', FL, BL, 'l', 'qb2')         # a prime was there: carry on
rule('qb1', BL, BL, '*', 'halt')       # empty interval: Legendre fails
rule('qb2', CW, CW, 'l', 'qb3')
home('qb3', 'qb4')
rule('qb4', LW, LW, 'r', 'qb5')
rule('qb5', K, K, 'r', 'qb5')
rule('qb5', BL, BL, 'r', 'qb5')
rule('qb5', SW, SW, '*', 'iq0')          # n += 1, countdown grows with it
increment('iq', 'qb7')
rule('qb7', SW, SW, 'r', 'qb7')
rule('qb7', K, K, 'r', 'qb7')
rule('qb7', MK, MK, 'r', 'qb7')
rule('qb7', D, BL, 'r', 'qb7')
rule('qb7', BL, BL, 'r', 'qb7')
rule('qb7', CW, CW, 'r', 'qb8')
rule('qb8', BL, BL, 'l', 'qb9')
rule('qb8', FL, BL, 'l', 'qb9')
home('qb9', 'fb0')
fill('fb', 2, 'qa0')                    # C = 2n again
for s in PASS:
    rule('qa0', s, s, 'r', 'qa0')
rule('qa0', ML, LIVE, 'r', 'q1')
rule('qa0', MM, COMP, 'r', 'q1')

# ------------------------------------------------------------- grow the line
# x6: walk home, then append five cells at the right end and start over
for sym in [LIVE, COMP, FW]:
    rule('x6', sym, sym, 'l', 'x6')
rule('x6', FL, FL, 'l', 'x6')
rule('x6', CW, CW, 'l', 'x6')
for sym in [BL, D, SW, MK, K]:
    rule('x6', sym, sym, 'l', 'x6')
rule('x6', LW, LW, 'r', 'x7')
for sym in [K, MK, SW, D, BL, CW, FL, FW]:
    rule('x7', sym, sym, 'r', 'x7')
for sym in [LIVE, COMP]:
    rule('x7', sym, sym, 'r', 'x7')
rule('x7', LW, LW, 'r', 'x7')
rule('x7', RW, LIVE, 'r', 'x8')
rule('x8', BL, LIVE, 'r', 'x9')
rule('x9', BL, LIVE, 'r', 'x10')
rule('x10', BL, LIVE, 'r', 'x11')
rule('x11', BL, LIVE, 'r', 'x12')
rule('x12', BL, RW, 'l', 'x13')
home('x13', 'r1')


def machine():
    return '\n'.join(R) + '\n'


def start_tape(length=8, composites=()):
    cells = [COMP, COMP] + [LIVE] * (length - 2)
    for i in composites:
        cells[i] = COMP
    return (LW + K + K + SW + BL * 40 + CW + BL + FW + ''.join(cells) + RW)


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('legendre.txt', 'w').write(text)
    print('rules %d  states %d' % (len(text.splitlines()), len({r.split()[0] for r in text.splitlines()})))
    s = Session(0, None, morphett=text, init=start_tape(9))
    i = s.advance(140000)
    print('sim step', i['step'], 'cells', i['ones'], 'span', i['lo'], i['hi'],
          'states seen', len({r.split()[0] for r in text.splitlines()}))
    draw(s.snapshot()).save('legendre.png')
