"""Phase-start dynamics of the accelerated #758 map, for finding a telescoping invariant.

Prints, per phase: region, length, a, c, Q = a+2c, and the ratios that the per-phase
charges are built from (Q/(2c) for L, Q/(a+1) for j).
"""
import sys

from _cyc import step


def phases(a, c, cap=40000):
    c0 = c
    t = 0
    cur = None
    out = []
    while t < cap:
        reg = 'J' if a <= c else 'L'
        if reg != cur:
            cur = reg
            out.append({'reg': reg, 'a': a, 'c': c, 'len': 0, 't': t})
        out[-1]['len'] += 1
        nx = step(a, c)
        if nx is None:
            return out, t + 1, 'halt'
        a, c = nx
        t += 1
        if a == 1:
            return out, t, 'a1'
        if 2 * c <= c0:
            return out, t, 'c-halved'
    return out, t, 'cap'


def report(k, c):
    a0 = 2 * 3 ** k - 1
    ph, T, why = phases(a0, c)
    print('k=%d c=%d  T=%d  %s  phases=%d' % (k, c, T, why, len(ph)))
    print('  idx reg  len        log2(a)      log2(c)     a/c      Q/(2c)   Q/(a+1)')
    for i, p in enumerate(ph):
        a, cc = p['a'], p['c']
        q = a + 2 * cc
        print('  %3d  %s  %4d  %12.2f %12.2f %9.3f %9.3f %9.3f'
              % (i, p['reg'], p['len'],
                 a.bit_length(), cc.bit_length(), a / cc, q / (2 * cc), q / (a + 1)))
    print()


if __name__ == '__main__':
    report(7, 24)
    report(289, 2047)
    report(292, 471656)
    report(20, 2047)
