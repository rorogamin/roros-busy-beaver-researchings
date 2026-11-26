import math
from t758_dyn import rule, step, HALT, halving_time, phase_list

def l10(x):
    if x <= 0: return float('-inf')
    n = len(str(x))
    return (n - 1) + math.log10(x / 10 ** (n - 1))

def rep(k, c0, verbose=True):
    A = 2 * 3 ** k - 1
    ph, why = phase_list(A, c0)
    T, stop = halving_time(A, c0)
    Q0 = A + 2 * c0
    print('k=%d c0=%d  T=%d stop=%s phases=%d  log10 Q0=%.3f' % (k, c0, T, stop, len(ph), l10(Q0)))
    starts = []
    for i, (side, n, a, cc) in enumerate(ph):
        Q = a + 2 * cc
        s = 2 * cc / Q
        starts.append((side, n, s, cc))
        if verbose:
            print('   %2d %s len=%4d  s=2c/Q=%.6e   log10 c=%8.3f  log1.5(1/s)=%7.2f  actual=%d'
                  % (i, side, n, s, l10(cc), math.log(1 / s) / math.log(1.5) if s > 0 else -1, n))
    ls = [s for (sd, n, s, cc) in starts if sd == 'L']
    print('    L-start s values:', ['%.4e' % x for x in ls])
    print('    sum of phase lens =', sum(n for (sd, n, s, cc) in starts))
    return T

print('### extremal (289,2047)')
rep(289, 2047)
print()
print('### (292,1)')
rep(292, 1)
