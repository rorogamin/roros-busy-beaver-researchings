"""Check that the two `P1` fractal rules cover the whole `P1` row of the census with
`r >= 1` (`ANALYSIS.md` §36, first row).

For every `B`-event of the real orbit whose tape word begins
`U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · …`, the script determines whether the token
that absorbs the carry comes immediately after the inner `u` (the shape of
`rule_P1_fractal`) or after a further run of `s+1` tokens `u` (the shape of
`rule_P1_fractal_gen`), and prints the counts together with the parameter ranges that
actually occur.

Exploratory only; nothing here is machine-checked.
"""

import sys
from collections import Counter
from be3 import run


def classify(toks):
    """Return ('imm', r, m) or ('gen', r, s, m) or None."""
    if len(toks) < 6 or toks[0] != ('U', 2, 1) or toks[1] != ('U', 4, 1):
        return None
    i = 2
    r1 = 0
    while i < len(toks) and toks[i] == ('U', 1, 1):
        r1 += 1
        i += 1
    if r1 == 0 or i + 2 >= len(toks):
        return None
    if toks[i] != ('U', 2, 2) or toks[i + 1] != ('V', 1) or toks[i + 2] != ('U', 1, 1):
        return None
    i += 3
    s1 = 0
    while i < len(toks) and toks[i] == ('U', 1, 1):
        s1 += 1
        i += 1
    if i >= len(toks):
        return None
    t = toks[i]
    if t[0] != 'U' or t[1] != 1 or t[2] % 2 != 0 or t[2] < 2:
        return None
    m = (t[2] - 2) // 2
    if s1 == 0:
        return ('imm', r1 - 1, m)
    return ('gen', r1 - 1, s1 - 1, m)


if __name__ == '__main__':
    ev = run(int(sys.argv[1]) if len(sys.argv) > 1 else 1000000)
    c = Counter()
    pars = {'imm': set(), 'gen': set()}
    for t, p, toks in ev:
        # the census row: prefix `P1`, at least one crossed `u`, and the inner
        # `U(2,2) V(1) u` that makes this the fractal row
        if not (len(toks) > 5 and toks[0] == ('U', 2, 1) and toks[1] == ('U', 4, 1)
                and toks[2] == ('U', 1, 1)):
            continue
        i = 2
        while i < len(toks) and toks[i] == ('U', 1, 1):
            i += 1
        if not (i + 2 < len(toks) and toks[i] == ('U', 2, 2) and toks[i + 1] == ('V', 1)
                and toks[i + 2] == ('U', 1, 1)):
            continue
        cl = classify(toks)
        if cl is None:
            c['UNCOVERED'] += 1
            print('uncovered at step %d: %s' % (t, toks))
        else:
            c[cl[0]] += 1
            pars[cl[0]].add(cl[1:])
    print('P1 rows with the inner U(2,2) V(1):', dict(c))
    for k in ('imm', 'gen'):
        if pars[k]:
            print('%s parameters (r, [s,] m): %s' % (k, sorted(pars[k])))
