"""Stage decomposition of the `P3` rule with a crossed `U(2,1)`, an absorbing `U(1,even)`
and a `V(2c+5)` after it (`sim/u21v.py` finds the rule; this script cuts the computation
into the passes a Lean proof composes).

It prints the configuration at every turning point of the head, together with the number
of steps since the previous one.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T, U, V, u


def word(r, s, m, c, w, mp):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + u * r + U(2, 1) + u * s + U(1, 2 * m + 2)
            + V(2 * c + 5) + u * w + U(1, 2 * mp + 2) + [0])


def out(r, s, m, c, w, mp):
    return (U(2, 1) + U(4, 1) + u * r + U(1, 4) + u * s + U(1, 2 * m + 4)
            + V(2 * c + 3) + u * w + U(1, 2 * mp + 4) + [0])


def steps(r, s, m, c, w, mp):
    return 137 + 12 * r + 6 * s + 10 * m + 10 * c + 6 * w + 10 * mp


def turning_points(l):
    """Yield (steps_since_last, state, pos, tape) at every change of direction."""
    l = list(l)
    q, k = 'B', 3
    prev_dir = 0
    last = 0
    n = 0
    res = [(0, q, k, list(l))]
    while not (q == 'B' and k == 0 and n > 0):
        wr, d, s = T[(q, l[k])]
        l[k] = wr
        k += d
        q = s
        n += 1
        if d != prev_dir:
            res.append((n - last, q, k, list(l)))
            last = n
            prev_dir = d
        if n > 100000:
            break
    res.append((n - last, q, k, list(l)))
    return res


def show(r, s, m, c, w, mp):
    print('--- r=%d s=%d m=%d c=%d w=%d mp=%d, %d steps' % (r, s, m, c, w, mp,
                                                            steps(r, s, m, c, w, mp)))
    for (d, q, k, l) in turning_points(word(r, s, m, c, w, mp)):
        print('  +%-4d %s %2d  %s' % (d, q, k, ''.join(map(str, l))))


def check(rng=3):
    bad = 0
    for r in range(rng):
        for s in range(rng):
            for m in range(rng):
                for c in range(rng):
                    for w in range(rng):
                        for mp in range(rng):
                            l = word(r, s, m, c, w, mp)
                            q, k, n = 'B', 3, steps(r, s, m, c, w, mp)
                            lo, hi = k, k
                            ok = True
                            for _ in range(n):
                                t = T[(q, l[k])]
                                if t is None:
                                    ok = False
                                    break
                                wr, d, st = t
                                l[k] = wr
                                k += d
                                q = st
                                lo, hi = min(lo, k), max(hi, k)
                                if not (0 <= k < len(l)):
                                    ok = False
                                    break
                            if not (ok and q == 'B' and k == 0
                                    and l == out(r, s, m, c, w, mp)
                                    and lo == 0 and hi == len(l) - 1):
                                bad += 1
                                if bad < 5:
                                    print('MISMATCH', r, s, m, c, w, mp, q, k)
    print('mismatches:', bad)


if __name__ == '__main__':
    show(1, 1, 1, 1, 1, 1)
    check()


def stage_list(r, s, m, c, w, mp):
    """(name, steps, state and head offset at the end of the stage)."""
    return [
        ('carry_open', 22, 'A', 11),
        ('sweepR_042 x (r+1)', 3 * r + 3, 'A', 3 * r + 14),
        ('blockR 2', 4, 'A', 3 * r + 18),
        ('sweepR_042 x (s+1)', 3 * s + 3, 'A', 3 * r + 3 * s + 21),
        ('pingpong_chain0 m', 8 * m, 'A', 3 * r + 3 * s + 2 * m + 21),
        ('vcross_step', 12, 'A', 3 * r + 3 * s + 2 * m + 25),
        ('pingpong_chain0 (c+1)', 8 * c + 8, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 27),
        ('u2b_exit', 8, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 29),
        ('sweepR_042 x (w+1)', 3 * w + 3, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 32),
        ('cross_back mp', 10 * mp + 14, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 28),
        ('sweepL_bulk w', 3 * w, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 28),
        ('retV', 2, 'A', 3 * r + 3 * s + 2 * m + 2 * c + 26),
        ('run_ones_A (2c+5)', 2 * c + 5, 'A', 3 * r + 3 * s + 2 * m + 21),
        ('u2b_vturn', 4, 'A', 3 * r + 3 * s + 2 * m + 21),
        ('run_ones_A (2m+1)', 2 * m + 1, 'A', 3 * r + 3 * s + 20),
        ('sweepL_bulk (s+1)', 3 * s + 3, 'A', 3 * r + 17),
        ('blockL_1003', 6, 'A', 3 * r + 13),
        ('sweepL_bulk (r+1)', 3 * r + 3, 'A', 10),
        ('carry_reflect', 7, 'B', 11),
        ('sweepR_204 x (r+1)', 3 * r + 3, 'B', 3 * r + 14),
        ('u21_turn', 15, 'A', 3 * r + 11),
        ('sweepL_bulk r', 3 * r, 'A', 11),
        ('p3_final', 11, 'B', 0),
    ]


def check_stages(rng=3):
    bad = 0
    for r in range(rng):
        for s in range(rng):
            for m in range(rng):
                for c in range(rng):
                    for w in range(rng):
                        for mp in range(rng):
                            st = stage_list(r, s, m, c, w, mp)
                            assert sum(x[1] for x in st) == steps(r, s, m, c, w, mp), \
                                ('step sum', r, s, m, c, w, mp)
                            l = word(r, s, m, c, w, mp)
                            q, k = 'B', 3
                            for (nm, n, qq, kk) in st:
                                for _ in range(n):
                                    wr, d, sq = T[(q, l[k])]
                                    l[k] = wr
                                    k += d
                                    q = sq
                                if (q, k) != (qq, kk):
                                    bad += 1
                                    if bad < 6:
                                        print('STAGE MISMATCH', (r, s, m, c, w, mp), nm,
                                              q, k, 'expected', qq, kk)
                                    break
    print('stage mismatches:', bad)
