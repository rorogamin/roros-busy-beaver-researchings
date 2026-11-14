"""Stage decomposition of the `P1` row with an inner `U(2,2) V(1)` (`ANALYSIS.md` §36,
first row, first case), the decomposition that `RequestProject/FracP1.lean` turns into a
Lean proof.

`stages(r, m)` lists the twenty-eight macro steps as
`(name, number of steps, state and head offset at the end of the stage)`;
`check` replays them against the real machine for `0 <= r, m < rng` and also checks that
the step counts add up to `237 + 12r + 40m` and that the final word is the expected one.
`windows` prints, for each stage, the cells it touches and the words before and after —
this is what the `Win` windows in the Lean proof are read off from.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T
from p1fr import word0, out0, steps0


def stages(r, m):
    """(name, steps, state at the end, head offset at the end)."""
    return [
        ('p1g_open', 16, 'A', 13),
        ('sweepR_042 x (r+1)', 3 * r + 3, 'A', 3 * r + 16),
        ('blockR 2', 4, 'A', 3 * r + 20),
        ('fp1_turn12', 12, 'A', 3 * r + 24),
        ('sweepR_042', 3, 'A', 3 * r + 27),
        ('sweepR_042 (absorb)', 3, 'A', 3 * r + 30),
        ('cross_back m', 10 * m + 14, 'A', 3 * r + 26),
        ('sweepL_bulk 1', 3, 'A', 3 * r + 23),
        ('sweepL_bulk 1 (V)', 3, 'A', 3 * r + 20),
        ('fp1_turn2', 2, 'A', 3 * r + 22),
        ('sweepR_042 x 2', 6, 'A', 3 * r + 28),
        ('pingpong_chain0 (m+1)', 8 * m + 8, 'A', 3 * r + 2 * m + 30),
        ('rule_endgame', 9, 'B', 3 * r + 2 * m + 31),
        ('onesBack_gen 3 (2m+6)', 2 * m + 7, 'A', 3 * r + 24),
        ('fp1_ret4', 4, 'B', 3 * r + 20),
        ('fp1_ones3', 5, 'A', 3 * r + 15),
        ('sweepL_bulk (r+1)', 3 * r + 3, 'A', 12),
        ('fp1_two', 2, 'A', 10),
        ('fp1_reflect', 4, 'B', 10),
        ('sweepR_204 x (r+2)', 3 * r + 6, 'B', 3 * r + 16),
        ('fp1_crossU41', 7, 'A', 3 * r + 23),
        ('sweepR_042', 3, 'A', 3 * r + 26),
        ('cross_back (m+2)', 10 * m + 34, 'A', 3 * r + 22),
        ('fp1_two', 2, 'A', 3 * r + 20),
        ('fp1_reflect', 4, 'B', 3 * r + 20),
        ('sweepR_204', 3, 'B', 3 * r + 23),
        ('carry_B2', 1, 'A', 3 * r + 24),
        ('cross_back (m+3)', 10 * m + 44, 'A', 3 * r + 20),
        ('fp1_backL', 8, 'B', 3 * r + 12),
        ('sweepL_bulkB (r+1)', 3 * r + 3, 'B', 9),
        ('fp1_B1', 1, 'B', 8),
        ('fp1_pre', 4, 'A', 4),
        ('fp1_close', 6, 'B', 0),
    ]


def check(rng=4):
    bad = 0
    for r in range(rng):
        for m in range(rng):
            st = stages(r, m)
            tot = sum(x[1] for x in st)
            if tot != steps0(r, m):
                print('STEP SUM', r, m, tot, steps0(r, m))
                bad += 1
            l = list(word0(r, m))
            q, k = 'B', 3
            for (nm, n, qq, kk) in st:
                for _ in range(n):
                    wr, d, s = T[(q, l[k])]
                    l[k] = wr
                    k += d
                    q = s
                if (q, k) != (qq, kk):
                    print('STAGE', r, m, nm, q, k, 'expected', qq, kk)
                    bad += 1
                    break
            if l != out0(r, m):
                print('OUT', r, m)
                bad += 1
    print('mismatches:', bad)


def windows(r=2, m=2):
    l = list(word0(r, m))
    q, k = 'B', 3
    for (nm, n, qq, kk) in stages(r, m):
        lo = hi = k
        q0, k0 = q, k
        before = list(l)
        for _ in range(n):
            wr, d, s = T[(q, l[k])]
            l[k] = wr
            k += d
            q = s
            lo, hi = min(lo, k), max(hi, k)
        print('%-22s %3d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
              % (nm, n, q0, k0, q, k, lo, hi))
        print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
        print('    out: %s' % ''.join(map(str, l[lo:hi + 1])))


if __name__ == '__main__':
    check()
    print()
    windows()
