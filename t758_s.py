import sys, math
from t758_dyn import rule, step, HALT, halving_time, phase_list

def l10(x):
    if x <= 0: return float('-inf')
    return (len(str(x)) - 1) + math.log10(x / 10 ** (len(str(x)) - 1))

def phases_report(A, c):
    ph, why = phase_list(A, c)
    T, stop = halving_time(A, c)
    print('k, c0=%d  T=%d  stop=%s  phases=%d' % (c, T, stop, len(ph)))
    print('  i side len   log10s      s=2c/Q        n_pred=log1.5(1/s)  m_pred=log3(1/(1-s))')
    tot = 0
    for i, (side, n, a, cc) in enumerate(ph):
        Q = a + 2 * cc
        s = 2 * cc / Q
        print('  %2d  %s %4d  %9.4f  %11.4e   %8.2f  %8.2f   (actual %d)' % (
            i, side, n, l10(s), s,
            (math.log(1 / s) / math.log(1.5)) if s > 0 else -1,
            (math.log(1 / (1 - s)) / math.log(3)) if s < 1 else -1, n))
        tot += n
    print('  total', tot)
    return T

print('=== c0 = 1, k = 292 ===')
k = 292
A = 2 * 3 ** k - 1
phases_report(A, 1)
print()
print('=== c0 scan (small c0, k=292) ===')
for c0 in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095]:
    T, why = halving_time(A, c0)
    print('  c0=%-6d T=%-6d stop=%s' % (c0, T, why))
