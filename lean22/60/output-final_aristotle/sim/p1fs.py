"""Stage decomposition of the `P1` fractal row with intervening tokens
(`ANALYSIS.md` §36, first row, second case), the decomposition that
`RequestProject/FracP1s.lean` turns into a Lean proof.

`stages(r, s, m)` lists the macro steps of the first two passes as
`(name, number of steps, state and head offset at the end of the stage)`.
`check` replays them against the real machine and reports the first stage whose
end state/position disagrees; `windows` prints the cells each stage touches
together with the words before and after, which is what the `Win` windows in the
Lean proof are read off from.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T
from p1fr import word1, out1, steps1


def stages(r, s, m):
    """(name, steps, state at the end, head offset at the end)."""
    return [
        ('p1g_open', 16, 'A', 13),
        ('sweepR_042 x (r+1)', 3 * r + 3, 'A', 3 * r + 16),
        ('blockR 2', 4, 'A', 3 * r + 20),
        ('fp1_turn12', 12, 'A', 3 * r + 24),
        ('sweepR_042 x (s+2)', 3 * s + 6, 'A', 3 * r + 3 * s + 30),
        ('sweepR_042 (absorb)', 3, 'A', 3 * r + 3 * s + 33),
        ('cross_back m', 10 * m + 14, 'A', 3 * r + 3 * s + 29),
        ('sweepL_bulk (s+2)', 3 * s + 6, 'A', 3 * r + 23),
        ('sweepL_bulk 1 (V)', 3, 'A', 3 * r + 20),
        ('fp1_turn2', 2, 'A', 3 * r + 22),
        ('sweepR_042 x (s+3)', 3 * s + 9, 'A', 3 * r + 3 * s + 31),
        ('pingpong_chain0 (m+1)', 8 * m + 8, 'A', 3 * r + 3 * s + 2 * m + 33),
        ('rule_endgame', 9, 'B', 3 * r + 3 * s + 2 * m + 34),
        ('onesBack_gen 3 (2m+6)', 2 * m + 7, 'A', 3 * r + 3 * s + 27),
        ('fp1_ret4', 4, 'B', 3 * r + 3 * s + 23),
        ('sweepL_bulkB (s+1)', 3 * s + 3, 'B', 3 * r + 20),
    ]


def stages2(r, s, m):
    """Passes three and four, and the return to the left end."""
    return [
        ('fp1_ones3', 5, 'A', 3 * r + 15),
        ('sweepL_bulk (r+1)', 3 * r + 3, 'A', 12),
        ('fp1_two', 2, 'A', 10),
        ('fp1_reflect', 4, 'B', 10),
        ('sweepR_204 x (r+2)', 3 * r + 6, 'B', 3 * r + 16),
        ('fp1_crossU41', 7, 'A', 3 * r + 23),
        ('sweepR_042 x (s+2)', 3 * s + 6, 'A', 3 * r + 3 * s + 29),
        ('cross_back (m+2)', 10 * m + 34, 'A', 3 * r + 3 * s + 25),
        ('sweepL_bulk (s+1)', 3 * s + 3, 'A', 3 * r + 22),
        ('fp1_two', 2, 'A', 3 * r + 20),
        ('fp1_reflect', 4, 'B', 3 * r + 20),
        ('sweepR_204 x (s+2)', 3 * s + 6, 'B', 3 * r + 3 * s + 26),
        ('carry_B2', 1, 'A', 3 * r + 3 * s + 27),
        ('cross_back (m+3)', 10 * m + 44, 'A', 3 * r + 3 * s + 23),
        ('sweepL_bulk (s+1) [2nd]', 3 * s + 3, 'A', 3 * r + 20),
        ('fp1_backL', 8, 'B', 3 * r + 12),

        ('sweepL_bulkB (r+1)', 3 * r + 3, 'B', 9),
        ('fp1_B1', 1, 'B', 8),
        ('fp1_pre', 4, 'A', 4),
        ('fp1_close', 6, 'B', 0),
    ]


def replay(r, s, m, st=None, verbose=False):
    """Replay the stage list; return the list of (stage, state, head) reached."""
    st = st if st is not None else stages(r, s, m)
    l = list(word1(r, s, m))
    q, k = 'B', 3
    out = []
    for (nm, n, qq, kk) in st:
        lo = hi = k
        q0, k0 = q, k
        before = list(l)
        for _ in range(n):
            t = T[(q, l[k])]
            if t is None:
                print('HALT in', nm)
                return out
            w, d, sq = t
            l[k] = w
            k += d
            q = sq
            lo, hi = min(lo, k), max(hi, k)
        out.append((nm, q, k))
        if verbose:
            print('%-22s %3d steps  %s%-3d -> %s%-3d  cells [%d,%d]'
                  % (nm, n, q0, k0, q, k, lo, hi))
            print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
            print('    out: %s' % ''.join(map(str, l[lo:hi + 1])))
        if (q, k) != (qq, kk):
            print('STAGE MISMATCH', nm, 'got', q, k, 'expected', qq, kk)
            return out
    print('total steps', sum(x[1] for x in st))
    return out


def full(r, s, m):
    """The whole rule, for reference."""
    l = list(word1(r, s, m))
    q, k = 'B', 3
    for _ in range(steps1(r, s, m)):
        w, d, sq = T[(q, l[k])]
        l[k] = w
        k += d
        q = sq
    print('end', q, k, 'ok' if l == out1(r, s, m) else 'BAD')


def boundary(r, s, m):
    """The tape word and head position after pass 1-2 and after pass 3-4."""
    l = list(word1(r, s, m))
    q, k = 'B', 3
    st = stages(r, s, m) + stages2(r, s, m)
    cuts = {len(stages(r, s, m)) - 1: 'after passes 1-2',
            len(st) - 6: 'after passes 3-4'}
    for i, (nm, n, qq, kk) in enumerate(st):
        for _ in range(n):
            w, d, sq = T[(q, l[k])]
            l[k] = w
            k += d
            q = sq
        if i in cuts:
            print('%s: %s%d' % (cuts[i], q, k))
            print('  ' + ''.join(map(str, l)))


def checkall(rng=3):
    bad = 0
    for r in range(rng):
        for s in range(rng):
            for m in range(rng):
                st = stages(r, s, m) + stages2(r, s, m)
                if sum(x[1] for x in st) != steps1(r, s, m):
                    print('STEP SUM', r, s, m)
                    bad += 1
                l = list(word1(r, s, m))
                q, k = 'B', 3
                for (nm, n, qq, kk) in st:
                    for _ in range(n):
                        w, d, sq = T[(q, l[k])]
                        l[k] = w
                        k += d
                        q = sq
                    if (q, k) != (qq, kk):
                        print('STAGE', r, s, m, nm, q, k, 'expected', qq, kk)
                        bad += 1
                        break
                if l != out1(r, s, m):
                    print('OUT', r, s, m)
                    bad += 1
    print('mismatches:', bad)


if __name__ == '__main__':
    full(1, 1, 1)
    replay(1, 1, 1, st=stages(1, 1, 1) + stages2(1, 1, 1), verbose=True)
    checkall()
    boundary(1, 1, 1)
    boundary(2, 1, 1)
    boundary(1, 2, 1)
    boundary(1, 1, 2)
