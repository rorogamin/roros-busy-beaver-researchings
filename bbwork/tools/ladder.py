"""Ladder machine: boot -> core -> connector -> core -> ... halted by a fuel block.

Tape layout:  0^inf  [fuel 1^b]  0 0  [C 1^c]  0  [U]  0  [W]  0^inf

Stage 1 runs the doubling core with counter C.  The connector then reuses the
output block W as the next counter, writes a fresh U,W pair after it, walks left
to the fuel, erases one fuel cell, and re-enters the core.  When the fuel runs
out the machine halts (undefined transition).  So the machine performs exactly b
stages, and each stage turns a counter of size n into 5*2^(n-1) ones: tower
height b.
"""
import tm
import mk_machines as mk

CORE = mk.core_table()

SCAN, INBLK = 40, 41
LS1, LS2, FK, FL, FD, FT, FG, FR = range(42, 50)
U1, U2, SEP1, W1 = range(50, 54)


def boot(b, c, u=2, w=1):
    pat = 'O' * b + 'ZZ' + 'O' * c + 'Z' + 'O' * u + 'Z' + 'O' * w
    n = len(pat)
    t = {(0, 0): (0, 'R', 15)}
    cells = [15 + i for i in range(n)]
    for i, ch in enumerate(pat):
        nxt = cells[i + 1] if i + 1 < n else 15 + n
        t[(cells[i], 0)] = (1 if ch == 'O' else 0, 'R', nxt)
    p = 15 + n
    q1, q2, q3, q4, q5 = p + 1, p + 2, p + 3, p + 4, p + 5
    t[(p, 0)] = (0, 'L', q1)
    t[(q1, 1)] = (1, 'L', q1); t[(q1, 0)] = (0, 'L', q2)
    t[(q2, 0)] = (0, 'L', q2); t[(q2, 1)] = (1, 'L', q3)
    t[(q3, 1)] = (1, 'L', q3); t[(q3, 0)] = (0, 'L', q4)
    t[(q4, 0)] = (0, 'L', q4); t[(q4, 1)] = (1, 'L', q5)
    t[(q5, 1)] = (1, 'L', q5); t[(q5, 0)] = (0, 'R', 13)
    return t, p + 6


def ladder(b, c, u=2, w=1):
    t, nxt = boot(b, c, u, w)
    t = dict(t)
    t.update(CORE)
    t[(12, 0)] = (0, 'R', SCAN)
    t[(SCAN, 0)] = (0, 'R', SCAN); t[(SCAN, 1)] = (1, 'R', INBLK)
    t[(INBLK, 1)] = (1, 'R', INBLK); t[(INBLK, 0)] = (0, 'R', U1)
    t[(U1, 0)] = (1, 'R', U2)                     # U = 1 1
    t[(U2, 0)] = (1, 'R', SEP1)
    t[(SEP1, 0)] = (0, 'R', W1)                   # separator
    t[(W1, 0)] = (1, 'R', LS1)                    # W = 1
    t[(LS1, 1)] = (1, 'L', LS1); t[(LS1, 0)] = (0, 'L', LS2)
    t[(LS2, 1)] = (1, 'L', LS1); t[(LS2, 0)] = (0, 'L', FK)
    t[(FK, 0)] = (0, 'L', FK); t[(FK, 1)] = (1, 'L', FL)
    t[(FL, 1)] = (1, 'L', FL); t[(FL, 0)] = (0, 'R', FD)
    t[(FD, 1)] = (0, 'R', FT)                     # erase leftmost fuel cell
    t[(FT, 1)] = (1, 'R', FG)                     # fuel remains
    t[(FG, 1)] = (1, 'R', FG); t[(FG, 0)] = (0, 'R', FR)
    t[(FR, 0)] = (0, 'R', FR); t[(FR, 1)] = (1, 'R', 13)
    return t, max(nxt, 54)


if __name__ == '__main__':
    import sys
    for b, c in ((1, 1), (1, 2), (1, 3), (2, 1)):
        tbl, n = ladder(b, c)
        m = tm.TM(n, tbl)
        steps, tape, head, state, halted = m.run(head=0, state=0, max_steps=int(sys.argv[1]) if len(sys.argv) > 1 else 200_000_000)
        print(f'b={b} c={c} states={n} steps={steps} halted={halted} score={m.score(tape)}')
