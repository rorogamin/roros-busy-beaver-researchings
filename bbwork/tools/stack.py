"""Growing-stack machine: an omega^k-rank descent with the stack depth as data.

Tape after boot (left to right, `0` blank, `1` mark):

    0^inf  [C 1^c]  00  [11 1^s1 0^.. 11]  0  [11 1^s2 0^.. 11]  0  ...

* `C` is the counter.  One round doubles it, and the doubling is done *leftward*:
  the engine copies `C` into blank tape on its left, behind a two-cell separator,
  then fills the separator, so `1^c` becomes `1^{2c+2}` and C's right edge never
  moves.  Growing into untouched tape on the left keeps the engine clear of the
  stack forever, and keeps the counter computable: `c -> 2c + 2`, so `r` rounds
  leave `3*2^(r+1) - 2` marks, where `r` is the total of the digits.
* A field is `11`, a block of `W` cells holding the digit (`1^s 0^{W-s}`), then a
  closing `11`.  Fixed width is what makes the walks position-independent: inside
  the stack every blank run is exactly one cell (the separator), and the only
  two-cell blank run is the counter gap.  Blanking a digit keeps the block's
  shape (`1^{s-1} 0^{W-s+1}`), so nothing inside a field ever looks like a gap.
* Every traversal *within* a field is counted by a state chain, never by symbol
  content: a block can hold zeros (padding, or a consumed digit), and an
  uncounted walk cannot tell those zeros from a separator.  Only the two
  structural tests use content: a blank after a field (separator vs gap) and a
  mark after that (another field vs the void).
* The field nearest C is S_1, so one round is one step of lexicographic descent:
  erase one digit of S_1; if S_1 has none, skip it and erase one digit of S_2;
  if every field is empty the numeral is 0 and the machine halts.  The rank is
  `omega^{k-1} s_k + ... + omega s_2 + s_1`, the depth `k` is data on the tape,
  and the family over `k` is the omega^omega family.

Digits must be at most `W`.  Deliberately not implemented (see the README on
Blueprint A): the push, which would let one run grow its own stack, and the
refill of an emptied field from the counter.  Both need free space *inside* the
stack, which a 2-symbol tape with single-blank separators does not have.
"""
import tm

W = 3                     # digit block width; digits must satisfy 0 <= s <= W

ENTRY = 200
HLT = 199
E = [201 + i for i in range(11)]                  # engine
D0 = 220                                          # skip the counter gap
C = [221, 222, 223, 224]                          # o1, o2, b1, b2 (move right)
CB3, CB2, CB1 = 225, 226, 227                     # decisions at b3, b2, b1
EMP = [228 + i for i in range(6)]                 # o2, b1, b2, b3, c1, c2
NEXT, NEXT2 = 234, 235                            # after a field: blank, look
T1, T2, U1, V1 = 236, 237, 238, 239               # erase -> back to c2
X = [240 + i for i in range(7)]                   # c2, c1, b3, b2, b1, o2, o1
BL, BL2, CG = 247, 248, 249                       # leftward: blank, test, gap


def pattern(digits, c):
    pat = 'O' * c + 'ZZ'
    for s in digits:
        assert 0 <= s <= W
        pat += 'OO' + 'O' * s + 'Z' * (W - s) + 'OO' + 'Z'
    return pat


def build(digits, c):
    pat = pattern(digits, c)
    n = len(pat)
    t = {(0, 0): (0, 'R', 15)}

    # ---- boot: write the layout, one state per pattern cell -----------------
    cells = [15 + i for i in range(n)]
    for i, ch in enumerate(pat):
        nxt = cells[i + 1] if i + 1 < n else 15 + n
        t[(cells[i], 0)] = (1 if ch == 'O' else 0, 'R', nxt)

    # ---- boot: walk back left over the layout, one state per run -----------
    runs = []
    for ch in reversed(pat):
        if runs and runs[-1][0] == ch:
            runs[-1][1] += 1
        else:
            runs.append([ch, 1])
    walk = [15 + n + i for i in range(len(runs))]
    for i, (ch, _) in enumerate(runs):
        st = walk[i]
        other = walk[i + 1] if i + 1 < len(walk) else HLT
        same, diff = (0, 1) if ch == 'Z' else (1, 0)
        t[(st, same)] = (same, 'L', st)
        t[(st, diff)] = (diff, 'L', other)
    t[(walk[-1], 0)] = (0, 'R', ENTRY)   # past C's left edge: step back on

    # ---- engine: C := C ++ (11) ++ C, growing leftward ---------------------
    t[(ENTRY, 1)] = (1, 'R', ENTRY)      # walk right to C's right edge
    t[(ENTRY, 0)] = (0, 'L', E[0])
    t[(E[0], 1)] = (0, 'L', E[1])        # erase the cursor, move left
    t[(E[1], 1)] = (1, 'L', E[1])        # over the un-copied source
    t[(E[1], 0)] = (0, 'L', E[2])        # separator cell next to the source
    t[(E[2], 0)] = (0, 'L', E[3])        # second separator cell
    t[(E[3], 1)] = (1, 'L', E[3])        # over the destination
    t[(E[3], 0)] = (1, 'R', E[4])        # append one mark at its left end
    t[(E[4], 1)] = (1, 'R', E[4])        # back over the destination
    t[(E[4], 0)] = (0, 'R', E[5])        # at the separator
    t[(E[5], 0)] = (0, 'R', E[6])        # second separator cell
    t[(E[6], 1)] = (1, 'R', E[6])        # over the source to the cursor mark
    t[(E[6], 0)] = (1, 'L', E[7])        # restore the mark
    t[(E[7], 1)] = (0, 'L', E[1])        # next cell to copy: same body as E[0]
    t[(E[7], 0)] = (1, 'L', E[8])        # source exhausted: fill separators
    t[(E[8], 0)] = (1, 'L', E[9])        # second separator cell, filled
    t[(E[9], 1)] = (1, 'R', E[9])        # walk right over the doubled counter
    t[(E[9], 0)] = (0, 'R', E[10])       # first blank of the counter gap
    t[(E[10], 0)] = (0, 'R', D0)         # second blank: into the stack

    # ---- decrement: erase one digit of the nearest non-empty field ---------
    t[(D0, 0)] = (0, 'R', D0)            # over blanks to the opening `11`
    t[(D0, 1)] = (1, 'R', C[0])
    for a, b in zip(C, C[1:]):           # o1, o2, b1: counted moves to b2
        t[(a, 0)] = (0, 'R', b)
        t[(a, 1)] = (1, 'R', b)
    t[(C[3], 0)] = (0, 'L', CB2)         # b3 is the first decision
    t[(C[3], 1)] = (0, 'R', T1)

    # decisions, rightmost block cell first
    t[(CB3, 1)] = (0, 'R', T1)           # erase here, then back to the end
    t[(CB3, 0)] = (0, 'L', CB2)
    t[(CB2, 1)] = (0, 'R', U1)
    t[(CB2, 0)] = (0, 'L', CB1)
    t[(CB1, 1)] = (0, 'R', V1)
    t[(CB1, 0)] = (0, 'L', EMP[0])       # no digit: skip the whole field

    # back to the closing `11`, then run the leftward chain
    t[(T1, 0)] = (0, 'R', T2)
    t[(T1, 1)] = (1, 'R', T2)
    t[(T2, 0)] = (0, 'L', X[1])
    t[(T2, 1)] = (1, 'L', X[1])
    t[(U1, 0)] = (0, 'R', T1)
    t[(U1, 1)] = (1, 'R', T1)
    t[(V1, 0)] = (0, 'R', U1)
    t[(V1, 1)] = (1, 'R', U1)

    # skip an empty field: o2 -> c2, then one blank, then the next opening `11`
    for a, b in zip(EMP, EMP[1:]):
        t[(a, 0)] = (0, 'R', b)
        t[(a, 1)] = (1, 'R', b)
    t[(EMP[-1], 0)] = (0, 'R', NEXT)
    t[(EMP[-1], 1)] = (1, 'R', NEXT)
    t[(NEXT, 0)] = (0, 'R', NEXT2)
    t[(NEXT2, 1)] = (1, 'R', C[0])       # another field follows (C[0] is the o2 state)
    # (NEXT2, 0) undefined: two blanks in a row is the end of the stack -> halt

    # leftward chain: c2 -> c1 -> b3 -> b2 -> b1 -> o2 -> o1 -> the blank before
    for a, b in zip(X, X[1:]):
        t[(a, 0)] = (0, 'L', b)
        t[(a, 1)] = (1, 'L', b)
    t[(X[-1], 0)] = (0, 'L', BL)
    t[(X[-1], 1)] = (1, 'L', BL)
    t[(BL, 0)] = (0, 'L', BL2)           # step off the separator
    t[(BL2, 1)] = (1, 'L', X[1])         # another field to cross
    t[(BL2, 0)] = (0, 'L', CG)           # second blank: the counter gap
    t[(CG, 0)] = (0, 'L', CG)
    t[(CG, 1)] = (1, 'R', ENTRY)
    return t, max(250, 15 + n + len(runs) + 1)


def score_of(digits, c=1):
    """Predicted halt score: counter after the final, wasted doubling."""
    r = sum(digits)
    return 3 * 2 ** (r + 1) - 2 + 4 * len(digits)


if __name__ == '__main__':
    import sys
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 50_000_000
    bad = 0
    for digits, c in (([1], 1), ([2], 1), ([1, 1], 1), ([2, 1], 1),
                      ([2, 2], 1), ([3, 2], 1), ([2, 2, 2], 1), ([3, 3, 2], 1),
                      ([2, 2, 2, 2], 1)):
        tbl, n = build(digits, c)
        m = tm.TM(n, tbl)
        steps, tape, head, state, halted = m.run(head=0, state=0, max_steps=cap)
        got, want = m.score(tape), score_of(digits, c)
        ok = halted and got == want
        bad += 0 if ok else 1
        print('digits=%-12s states=%3d steps=%8d halted=%-5s score=%6d '
              'expect=%6d %s'
              % (digits, n, steps, halted, got, want, 'OK' if ok else 'MISMATCH'))
    print('ALL OK' if not bad else '%d FAILED' % bad)
