"""Check which steps of the `P3`/`U(2,8)`/`V` census row `rule_P3_U2b_V` covers
(`ANALYSIS.md` §36, second row).

For every `B`-event of the real orbit whose tape word begins
`U(2,2) V(1) u · U(2,even) V(1) · u^k · U(1,even) …` the script records the exponent of
the absorbing token, the number `k` of tokens `u` after the `V(1)`, and the exponent of
the token that stops the carry.  `rule_P3_U2b_V` is the case `absorbing = U(2,8)` and
`k >= 3`.

Exploratory only; nothing here is machine-checked.
"""

import sys
from collections import Counter
from be3 import run


def classify(toks):
    """Return ('cov', t, m), ('short', k, m), ('other', a, b) or None."""
    if len(toks) < 5 or toks[0] != ('U', 2, 2) or toks[1] != ('V', 1) \
            or toks[2] != ('U', 1, 1):
        return None
    ab = toks[3]
    if ab[0] != 'U' or len(toks) < 5 or toks[4] != ('V', 1):
        return None
    i = 5
    k = 0
    while i < len(toks) and toks[i] == ('U', 1, 1):
        k += 1
        i += 1
    if i >= len(toks):
        return None
    st = toks[i]
    if st[0] != 'U' or st[1] != 1 or st[2] % 2 != 0 or st[2] < 2:
        return None
    m = (st[2] - 2) // 2
    if (ab[1], ab[2]) != (2, 8):
        return ('other', ab[1], ab[2])
    if k < 3:
        return ('short', k, m)
    return ('cov', k - 3, m)


if __name__ == '__main__':
    ev = run(int(sys.argv[1]) if len(sys.argv) > 1 else 1000000)
    c = Counter()
    pars = set()
    for t, p, toks in ev:
        # the census row: prefix `P3`, absorbing token with `b >= 2`, a `V(1)` after it
        if not (len(toks) > 4 and toks[0] == ('U', 2, 2) and toks[1] == ('V', 1)
                and toks[2] == ('U', 1, 1) and toks[3][0] == 'U'
                and toks[3][2] >= 2 and toks[4] == ('V', 1)):
            continue
        cl = classify(toks)
        if cl is None:
            c['UNCOVERED'] += 1
            print('uncovered at step %d: %s' % (t, toks[:8]))
        else:
            c[cl[0]] += 1
            if cl[0] == 'cov':
                pars.add(cl[1:])
            elif cl[0] != 'cov':
                print('%s at step %d: %s' % (cl[0], t, toks[:8]))
    print('P3 rows with an absorbing U(2,b) and a V:', dict(c))
    print('rule_P3_U2b_V parameters (t, m):', sorted(pars))
