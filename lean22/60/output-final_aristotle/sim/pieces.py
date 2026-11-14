"""Check the fixed-size window rules used to assemble rule_P1 / rule_P3."""
from winchk import lrun

cases = [
    ('endgame',     'A', 2, [0,3,2,0]),
    ('p1_phase1',   'B', 3, [0,0,0,0,4,4,2,0,4,4,4,4,2,0,4,2,2]),
    ('p1_mid',      'A', 3, [0,0,0,3,2,2]),
    ('p1_final',    'A', 10, [0,1,3,1,0,0,3,1,0,1,3]),
    ('p3_phase1',   'B', 3, [0,0,0,0,4,4,2,2,4,3,2,0,4,2,0,4,2,2]),
    ('p3_mid',      'A', 6, [0,1,0,3,1,0,3,2,2]),
    ('p3_final',    'A', 11, [0,1,3,1,0,1,1,1,3,1,0,3]),
    ('B0left',      'B', 1, [1,0]),
]
for nm, q, k, l in cases:
    n, q2, k2, l2 = lrun(q, k, l)
    print('%-11s %s@%d %s  --%d-->  %s@%d %s' %
          (nm, q, k, l, n, q2, k2, l2))

# cross_back(n)
def U(a, b): return [0] + [4]*a + [2]*b
for n in range(0, 5):
    l = [3,1,0,3] + [2]*(2*n+1) + [0]
    r = lrun('A', 4, l)
    print('cross_back %d: %s --%d--> %s@%d %s   (expect %d)' %
          (n, l, r[0], r[3], r[2], r[1], 10*n+14))
