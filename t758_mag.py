import sys
from t758_dyn import rule, step, HALT, halving_time

def lg(x):
    s = str(x)
    if x == 0: return '-inf'
    return '%.4f' % (len(s) - 1 + __import__('math').log10(int(s[:18]) / 10 ** (len(s[:18]) - 1)))

def walk(A, c, cap=30):
    a, c = A, c
    print('%-3s %-6s %-10s %-10s %-10s %-6s %s' % ('i', 'rule', 'log10 a', 'log10 c', 'log10 Q', 'a/c', 'a+2c-Qstart'))
    Q0 = a + 2 * c
    for i in range(cap):
        r = rule(a, c)
        print('%-3d %-6s %-10s %-10s %-10s' % (i, r, lg(a), lg(c), lg(a + 2 * c)), end='')
        if a > 2 * c: print('   c<a/2')
        else: print('   %.4f' % (a / c if c else 0))
        if r is HALT: return
        a, c, h, _ = step(a, c)
        if h or a == 1: print('   STOP'); return

k = 289
A = 2 * 3 ** k - 1
print('=== extremal chain start, first 24 steps ===')
walk(A, 2047, 24)
print()
print('=== around the phase-0 -> phase-1 boundary ===')
a, c = A, 2047
for i in range(760):
    a, c, h, _ = step(a, c)
print('after 760 L steps:  log10 a=', lg(a), ' log10 c=', lg(c))
walk(a, c, 24)
