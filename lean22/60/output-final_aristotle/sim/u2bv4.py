"""Stage decomposition of the `P3` row with a `V` after an absorbing `U(2,8)`
(`ANALYSIS.md` §36, second row) — the decomposition a Lean proof follows.

The computation splits into six *fixed* stretches, in which the head stays inside the
first twenty-nine cells and the tape there does not depend on the parameters, and five
excursions into the run of `u`s and the token beyond it, each of which is a chain of the
sweeps, ping-pongs and turn-arounds the project already proves.

`stages(t, m)` lists them as `(name, steps, state and head cell at the end)`; `check`
replays the list against the real machine for `1 <= t <= 4`, `0 <= m <= 4`, and `windows`
prints, for each stage, the cells it touches and the words before and after.

Exploratory only; nothing here is machine-checked.
"""

import sys
from u21b import T
from u2bv2 import word, out, steps


def stages(t, m):
    """(name, steps, state at the end, head cell at the end); needs t >= 1."""
    return [
        ('open (fixed)', 65, 'A', 28),
        # --- excursion 1
        ('sweepR_042 x (t+3)', 3 * t + 9, 'A', 3 * t + 37),
        ('cross_back m', 10 * m + 14, 'A', 3 * t + 33),
        ('sweepL_bulk (t+2)', 3 * t + 6, 'A', 27),
        ('fixed 3', 7, 'B', 28),
        # --- excursion 2
        ('sweepR_204 x (t+2)', 3 * t + 6, 'B', 3 * t + 34),
        ('carry_B2', 1, 'A', 3 * t + 35),
        ('pingpong_chain0 (m+1)', 8 * m + 8, 'A', 3 * t + 2 * m + 37),
        ('rule_endgame', 9, 'B', 3 * t + 2 * m + 38),
        ('onesBack_gen 3 (2m+6)', 2 * m + 7, 'A', 3 * t + 31),
        ('sweepL_bulk (t+1)', 3 * t + 3, 'A', 28),
        ('one step', 1, 'B', 27),
        ('fixed 5', 41, 'B', 28),
        # --- excursion 3
        ('sweepR_420 x (t+1)', 3 * t + 3, 'B', 3 * t + 31),
        ('two steps 42 -> 03', 2, 'A', 3 * t + 33),
        ('pingpong_chain0 (m+2)', 8 * m + 16, 'A', 3 * t + 2 * m + 37),
        ('rule_endgame', 9, 'B', 3 * t + 2 * m + 38),
        ('onesBack_gen 3 (2m+8)', 2 * m + 9, 'A', 3 * t + 29),
        ('sweepL_bulk t', 3 * t, 'A', 29),
        ('two steps', 2, 'A', 27),
        ('fixed 7', 11, 'A', 28),
        # --- excursion 4
        ('sweepR_042 x (t+1)', 3 * t + 3, 'A', 3 * t + 31),
        ('cross_back (m+3)', 10 * m + 44, 'A', 3 * t + 27),
        ('sweepL_bulk t', 3 * t, 'A', 27),
        ('fixed 9', 17, 'B', 28),
        # --- excursion 5
        ('sweepR_204 x t', 3 * t, 'B', 3 * t + 28),
        ('carry_B2', 1, 'A', 3 * t + 29),
        ('pingpong_chain0 (m+4)', 8 * m + 32, 'A', 3 * t + 2 * m + 37),
        ('rule_endgame', 9, 'B', 3 * t + 2 * m + 38),
        ('onesBack_gen 3 (2m+12)', 2 * m + 13, 'A', 3 * t + 25),
        ('sweepL_bulk (t-1)', 3 * t - 3, 'A', 28),
        ('one step', 1, 'B', 27),
        ('close (fixed)', 57, 'B', 0),
    ]


def replay(t, m, verbose=False):
    l = list(word(t, m))
    q, k = 'B', 3
    st = stages(t, m)
    tot = sum(x[1] for x in st)
    if tot != steps(t, m):
        print('STEP SUM t=%d m=%d: %d vs %d' % (t, m, tot, steps(t, m)))
    for (nm, n, qq, kk) in st:
        q0, k0 = q, k
        before = list(l)
        lo = hi = k
        for _ in range(n):
            tr = T[(q, l[k])]
            if tr is None:
                print('HALT in', nm)
                return False
            w, d, s = tr
            l[k] = w
            k += d
            q = s
            lo, hi = min(lo, k), max(hi, k)
        if verbose:
            print('%-24s %4d steps  %s%-4d -> %s%-4d  cells [%d,%d]'
                  % (nm, n, q0, k0, q, k, lo, hi))
            print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
            print('    out: %s' % ''.join(map(str, l[lo:hi + 1])))
        if (q, k) != (qq, kk):
            print('STAGE t=%d m=%d %s: got %s%d, expected %s%d' % (t, m, nm, q, k, qq, kk))
            return False
    if l != out(t, m):
        print('OUT t=%d m=%d' % (t, m))
        return False
    return True


def check(trange=range(1, 5), mrange=range(0, 5)):
    bad = 0
    for t in trange:
        for m in mrange:
            if not replay(t, m):
                bad += 1
    print('mismatches:', bad)


if __name__ == '__main__':
    if len(sys.argv) > 2:
        replay(int(sys.argv[1]), int(sys.argv[2]), verbose=True)
    else:
        check()
