"""The `P3` macro step with a crossed `U(2,1)` and an absorbing `U(2,2m+4)`.

This is the census row "P3, r>=1 with one crossed exponent 2, absorb U(2,even), followed
by U" of `ANALYSIS.md` §31.  The script checks the rule and its stage decomposition.

Exploratory only; nothing here is machine-checked.
"""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}


def U(a, b): return [0] + [4] * a + [2] * b
def V(c):    return [4, 3] + [2] * c
u = U(1, 1)


def word(r, m):
    return [0, 0, 0] + U(2, 2) + V(1) + u + U(2, 1) + u * r + U(2, 2 * m + 4) + [0]


def out(r, m):
    return U(2, 1) + U(4, 1) + U(1, 4) + u * r + U(1, 2) + V(2 * m + 3) + [0]


def steps(r, m): return 107 + 6 * r + 10 * m


def trace(q, k, l, n):
    l = list(l); res = [(q, k, list(l))]
    for _ in range(n):
        w, d, s = T[(q, l[k])]
        l[k] = w; k += d; q = s
        res.append((q, k, list(l)))
    return res


def stages(r, m):
    """(name, steps, state and head offset at the end of the stage)"""
    return [('carry_open', 22, 'A', 11), ('sweepR_042', 3, 'A', 14),
            ('blockR 2', 4, 'A', 18), ('sweepR_042 x r', 3 * r, 'A', 3 * r + 18),
            ('blockR 2', 4, 'A', 3 * r + 22),
            ('turn_U2 (m+1)', 10 * m + 25, 'A', 3 * r + 21), ('retU2', 4, 'A', 3 * r + 17),
            ('sweepL_bulk r', 3 * r, 'A', 17), ('blockL_1003', 6, 'A', 13),
            ('sweepL_103', 3, 'A', 10), ('carry_reflect', 7, 'B', 11),
            ('sweepR_204', 3, 'B', 14), ('u21_turn', 15, 'A', 11),
            ('p3_final', 11, 'B', 0)]


if __name__ == '__main__':
    bad = 0
    for r in range(6):
        for m in range(6):
            n = steps(r, m)
            assert sum(x[1] for x in stages(r, m)) == n
            tr = trace('B', 3, word(r, m), n)
            q, k, l = tr[n]
            if (q, k, l) != ('B', 0, out(r, m)):
                bad += 1; print('MISMATCH', r, m, q, k, ''.join(map(str, l)))
            t = 0
            for nm, s, qq, kk in stages(r, m):
                t += s
                if tr[t][0] != qq or tr[t][1] != kk:
                    bad += 1
                    print('STAGE MISMATCH', r, m, nm, tr[t][0], tr[t][1], 'expected', qq, kk)
    print('mismatches:', bad)
