"""The `P1` macro step with `r >= 1` crossed tokens (ANALYSIS.md §36, first row).

In the real orbit this row always has an inner `U(2,2) V(1) u` — the prefix of a `P3`
configuration sitting inside the tape.  The head makes four passes, not two.

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


# --- the case in which the absorbing token comes straight after the inner `u`
def word0(r, m):
    return [0, 0, 0] + U(2, 1) + U(4, 1) + u * (r + 1) + U(2, 2) + V(1) + u + U(1, 2 * m + 2) + [0]


def out0(r, m):
    return U(2, 2) + u + U(2, 1) + u * (r + 2) + U(2, 2 * m + 10) + [0]


def steps0(r, m): return 237 + 12 * r + 40 * m


# --- the case in which at least one `u` intervenes
def word1(r, s, m):
    return ([0, 0, 0] + U(2, 1) + U(4, 1) + u * (r + 1) + U(2, 2) + V(1) + u + u * (s + 1)
            + U(1, 2 * m + 2) + [0])


def out1(r, s, m):
    return U(2, 2) + u + U(2, 1) + u * (r + 2) + U(2, 1) + u * s + U(1, 2 * m + 10) + [0]


def steps1(r, s, m): return 261 + 12 * r + 24 * s + 40 * m


if __name__ == '__main__':
    bad = 0
    for r in range(3):
        for m in range(3):
            res = run_win('B', 3, word0(r, m), steps0(r, m))
            if res[:3] != ('B', 0, out0(r, m)):
                bad += 1; print('MISMATCH 0', r, m, res[:2])
            for s in range(3):
                res = run_win('B', 3, word1(r, s, m), steps1(r, s, m))
                if res[:3] != ('B', 0, out1(r, s, m)):
                    bad += 1; print('MISMATCH 1', r, s, m, res[:2])
    print('mismatches:', bad)
