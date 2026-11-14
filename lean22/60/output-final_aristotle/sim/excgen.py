"""The three *general* excursions behind the five of `RequestProject/U2bV.lean`.

Reading the five excursions of `rule_P3_U2b_V` side by side shows that they are instances
of only three window rules, each with its own pair of parameters:

```
ExcA n m : A, offset 1 -> A, offset 0
    [3] ++ (042)^n ++ 2^(2m+1) ++ [0]  ->  [3] ++ (204)^(n-1) ++ 2^(2m+4) ++ [0]
    6n + 10m + 11 steps
ExcB n m : B, offset 1 -> B, offset 0
    [0] ++ (204)^n ++ 2^(2m+4) ++ [0]  ->  [0] ++ (420)^(n-1) ++ [4] ++ 2^(2m+6) ++ [0]
    6n + 10m + 23 steps
ExcC n m : B, offset 1 -> A, offset 0
    [1] ++ (420)^n ++ [4] ++ 2^(2m+6) ++ [0]  ->  [1] ++ (042)^n ++ 2^(2m+7) ++ [0]
    6n + 10m + 35 steps
```

The script checks all three over a range of parameters and reports the smallest `n` for
which each holds.

Exploratory only; nothing here is machine-checked.
"""

from u21b import T


def run_win(q, k, l, n):
    l = list(l)
    for _ in range(n):
        tr = T[(q, l[k])]
        if tr is None:
            return ('HALT',)
        w, d, s = tr
        l[k] = w; k += d; q = s
        if not (0 <= k < len(l)):
            return ('OUT',)
    return q, k, l


def excA(n, m):
    return ('A', [3] + [0, 4, 2] * n + [2] * (2 * m + 1) + [0],
            'A', [3] + [2, 0, 4] * (n - 1) + [2] * (2 * m + 4) + [0],
            6 * n + 10 * m + 11)


def excB(n, m):
    return ('B', [0] + [2, 0, 4] * n + [2] * (2 * m + 4) + [0],
            'B', [0] + [4, 2, 0] * (n - 1) + [4] + [2] * (2 * m + 6) + [0],
            6 * n + 10 * m + 23)


def excC(n, m):
    return ('B', [1] + [4, 2, 0] * n + [4] + [2] * (2 * m + 6) + [0],
            'A', [1] + [0, 4, 2] * n + [2] * (2 * m + 7) + [0],
            6 * n + 10 * m + 35)


if __name__ == '__main__':
    for nm, f in (('ExcA', excA), ('ExcB', excB), ('ExcC', excC)):
        ok = {}
        for n in range(1, 9):
            good = True
            for m in range(0, 6):
                q0, win, q1, wout, steps = f(n, m)
                if run_win(q0, 1, win, steps) != (q1, 0, wout):
                    good = False
            ok[n] = good
        print('%s: %s' % (nm, ' '.join('n=%d:%s' % (n, 'ok' if v else 'NO')
                                       for n, v in sorted(ok.items()))))
