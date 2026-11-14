"""A crossed `U(2,1)`, an absorbing `U(2,2m+4)` and a `V(1)` after it
(ANALYSIS.md §36, third row).

This is `rule_P3_U21_U2b` with a `V(1)` in place of the `0` that ends its window; the carry
is then not stopped at the absorbing token but is handed on, and a long run of `4`s — a
"virtual blank tape" in the sense of §24 — is created.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T, U, V, u


def run_win(q, k, l, n):
    l = list(l); mn = k; mx = k
    for _ in range(n):
        t = T[(q, l[k])]
        if t is None: return ('HALT',)
        w, d, s = t
        l[k] = w; k += d; q = s
        mn = min(mn, k); mx = max(mx, k)
        if not (0 <= k < len(l)): return ('OUT',)
    return q, k, l, mn, mx


def word(r, m, t, mp):
    return ([0, 0, 0] + U(2, 2) + V(1) + u + U(2, 1) + u * r + U(2, 2 * m + 4) + V(1)
            + u * (t + 1) + U(1, 2 * mp + 2) + [0])


def out(r, m, t, mp):
    return (U(2, 1) + U(4, 1) + U(1, 4) + u * (r + 1) + U(2 * m + 6, 1) + u * t
            + U(1, 2 * mp + 6) + [0])


def steps(r, m, t, mp): return 167 + 6 * r + 10 * m + 12 * t + 20 * mp


if __name__ == '__main__':
    bad = 0
    for r in range(4):
        for m in range(4):
            for t in range(3):
                for mp in range(3):
                    n = steps(r, m, t, mp)
                    res = run_win('B', 3, word(r, m, t, mp), n)
                    ok = (res[:3] == ('B', 0, out(r, m, t, mp)) and res[3] == 0
                          and res[4] == len(word(r, m, t, mp)) - 1)
                    if not ok:
                        bad += 1; print('MISMATCH', r, m, t, mp, res[:2])
    print('mismatches:', bad)
