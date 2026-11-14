"""Stage-by-stage check of the `P1` macro step with a `V` after the absorbing token.

Exploratory only; nothing here is machine-checked.
"""

from p1v import T, U, V, u, word, out, steps, trace


def stages(m, c, s, mp):
    """(name, number of steps) for each proposed stage."""
    return [
        ('p1g_open', 16),
        ('sweepR_042 x1', 3),
        ('pingpong_chain0 m', 8 * m),
        ('vcross_step', 12),
        ('pingpong_chain0 (c+1)', 8 * c + 8),
        ('u2b_exit', 8),
        ('sweepR_042 x(s+1)', 3 * s + 3),
        ('cross_back mp', 10 * mp + 14),
        ('sweepL_bulk s', 3 * s),
        ('retV', 2),
        ('run_ones_A (2c+5)', 2 * c + 5),
        ('u2b_vturn', 4),
        ('run_ones_A (2m+4)', 2 * m + 4),
        ('p1g_reflect', 8),
        ('p1g_B4', 1),
        ('carry_B2', 1),
        ('pingpong_chain0 (m+1)', 8 * m + 8),
        ('vcross_step', 12),
        ('pingpong_chain0 c', 8 * c),
        ('u2b_exit', 8),
        ('sweepR_042 x(s+1)', 3 * s + 3),
        ('cross_back (mp+1)', 10 * mp + 24),
        ('sweepL_bulk s', 3 * s),
        ('retV', 2),
        ('run_ones_A (2c+3)', 2 * c + 3),
        ('u2b_vturn', 4),
        ('run_ones_A (2m+6)', 2 * m + 6),
        ('p1v_back', 5),
        ('p1v_close', 7),
    ]


def show(m, c, s, mp):
    st = stages(m, c, s, mp)
    total = sum(n for _, n in st)
    print(f'--- m={m} c={c} s={s} mp={mp}   stage total {total}, '
          f'rule says {steps(m, c, s, mp)}')
    tr = trace('B', 3, word(m, c, s, mp), max(total, steps(m, c, s, mp)))
    t = 0
    q, k, l = tr[0]
    print(f'{"start":24s} t={t:5d} {q} @{k}  {"".join(map(str, l))}')
    for name, n in st:
        t += n
        q, k, l = tr[t]
        print(f'{name:24s} t={t:5d} {q} @{k}  {"".join(map(str, l))}')


if __name__ == '__main__':
    show(0, 0, 0, 0)
    show(1, 0, 0, 0)
