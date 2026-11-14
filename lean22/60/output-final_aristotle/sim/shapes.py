"""Classify each B-event macro step of the real orbit by the *shape* of the piece of
tape word that the step actually involves: the prefix phase, the run of tokens the
rightward pass crosses (all of which have b = 1), the first token with b >= 2 (the one
that absorbs the carry), and the token that follows it.

This says exactly which parametric macro rules a complete proof has to provide.
"""
import sys
from collections import Counter
from be3 import run
from toklib import name


def shape(toks):
    # prefix: P1 = U2,1 U4,1 ; P2 = U2,2 u ; P3 = U2,2 V1 u
    if toks[0] == ('U', 2, 1):
        ph, k = 'P1', 2
    elif toks[1][0] == 'V':
        ph, k = 'P3', 3
    else:
        ph, k = 'P2', 2
    rest = toks[k:]
    # tokens crossed by the rightward pass: those with b = 1 (U only)
    i = 0
    crossed = []
    while i < len(rest) and rest[i][0] == 'U' and rest[i][2] == 1:
        crossed.append(rest[i][1])
        i += 1
    absorb = rest[i] if i < len(rest) else None
    follow = rest[i + 1] if i + 1 < len(rest) else None
    return ph, tuple(crossed), absorb, follow


def cls(sh):
    ph, crossed, absorb, follow = sh
    ex = sorted(set(crossed) - {1})
    r0 = 'r=0' if len(crossed) == 0 else 'r>=1'
    a = 'none' if absorb is None else ('U(%d,%s)' % (absorb[1], 'even' if absorb[2] % 2 == 0 else 'odd')
                                       if absorb[0] == 'U' else 'V')
    f = 'none' if follow is None else follow[0]
    return (ph, r0, tuple(ex), a, f)


if __name__ == '__main__':
    ev = run(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
    c = Counter()
    for t, p, toks in ev:
        c[cls(shape(toks))] += 1
    for k, v in sorted(c.items(), key=lambda x: -x[1]):
        print('%6d  %s' % (v, k))
