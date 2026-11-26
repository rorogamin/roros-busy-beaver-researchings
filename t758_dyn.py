"""Phase structure and potential-function probe for BB(3,3) #758.

Exact rules (authoritative: M_758_Halving844.lean / BB33_758_Halving844.v):

  a: a > c, c%4 in {0,2}   -> (a-c-1,   3*(c//2)+2)          dQ=3
  b: a > c, c%4 == 1       -> (a-c-2,   3*((c-1)//2)+5)      dQ=5
  e: a > c, c%4 == 3, a=c+2-> (3c+8,    1)                   dQ=8
  c: a > c, c%4 == 3, else -> (a-c-4,   3*((c-1)//2)+8)      dQ=9
  h: a <= c, a even, c odd -> (1,       a//2+c+2)            dQ=5
  i: a <= c, a odd,  c even-> (3a,      c-a+4)               dQ=8
  j: a <= c, a odd,  c odd -> (3a+2,    c-a+1)               dQ=4
  halt in the remaining cases.
"""
import sys

HALT = 'HALT'

def rule(a, c):
    if a <= c:
        if a % 2 == 0:
            if c % 2 == 0: return HALT
            return 'h'
        if c % 2 == 0: return 'i'
        return 'j'
    if c % 4 in (0, 2): return 'a'
    if c % 4 == 1:
        if a == c + 1: return HALT
        return 'b'
    if a == c + 1: return HALT
    if a == c + 2: return 'e'
    if a == c + 3: return HALT
    return 'c'

def step(a, c):
    r = rule(a, c)
    if r is HALT: return (0, 0, True, HALT)
    if r == 'h':  return (1, a // 2 + c + 2, False, r)
    if r == 'i':  return (3 * a, c - a + 4, False, r)
    if r == 'j':  return (3 * a + 2, c - a + 1, False, r)
    if r == 'a':  return (a - c - 1, 3 * (c // 2) + 2, False, r)
    if r == 'b':  return (a - c - 2, 3 * ((c - 1) // 2) + 5, False, r)
    if r == 'e':  return (3 * c + 8, 1, False, r)
    if r == 'c':  return (a - c - 4, 3 * ((c - 1) // 2) + 8, False, r)
    raise AssertionError

LEFT = set('abce')

def trace(a, c, cap=40000):
    """list of (rule, a, c) at each step."""
    out = []
    for _ in range(cap):
        r = rule(a, c)
        out.append((r, a, c))
        if r is HALT: break
        a, c, h, _ = step(a, c)
        if h or a == 1: break
    return out

def halving_time(a, c, c0=None, cap=40000):
    if c0 is None: c0 = c
    n = 0
    for _ in range(cap):
        r = rule(a, c)
        if r is HALT: return n + 1 if False else n + 1, 'halt'
        a2, c2, h, _ = step(a, c)
        n += 1
        if h: return n, 'halt'
        if a2 == 1: return n, 'a=1'
        if 2 * c2 <= c0: return n, 'c-halved'
        a, c = a2, c2
    return cap, 'cap'

def phase_list(a, c, c0=None, cap=40000):
    """maximal runs of LEFT / RIGHT rules until the ht stop condition."""
    if c0 is None: c0 = c
    ph = []
    cur = None
    n = 0
    for _ in range(cap):
        r = rule(a, c)
        if r is HALT:
            ph.append((cur or 'HALT', n, a, c)); return ph, 'halt'
        side = 'L' if r in LEFT else 'J'
        if side != cur:
            if cur is not None: ph.append((cur, n, a0, c0s))
            cur, n, a0, c0s = side, 0, a, c
        a2, c2, h, _ = step(a, c)
        n += 1
        if h:
            ph.append((cur, n, a0, c0s)); return ph, 'halt'
        if a2 == 1 or 2 * c2 <= c0:
            ph.append((cur, n, a0, c0s)); return ph, ('a=1' if a2 == 1 else 'c-half')
        a, c = a2, c2
    ph.append((cur, n, a0, c0s))
    return ph, 'cap'

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'ext'

    if mode == 'ext':
        k, c = 289, 2047
        A = 2 * 3 ** k - 1
        ph, why = phase_list(A, c)
        T, stop = halving_time(A, c)
        print('k=%d c=%d  T=%d stop=%s phases=%d' % (k, c, T, stop, len(ph)))
        print('  #   side  len        a_start                 c_start          Q_start')
        for i, (side, n, a, cc) in enumerate(ph):
            print('  %2d   %s   %4d   %s  %s  %s' % (i, side, n, a, cc, a + 2 * cc))
        # per-step dQ profile
        tr = trace(A, c)
        from collections import Counter
        print('  rule counts:', Counter(r for r, _, _ in tr))
        dqs = Counter()
        for i in range(len(tr) - 1):
            _, a1, c1 = tr[i]; _, a2, c2 = tr[i + 1]
            dqs[(a2 + 2 * c2) - (a1 + 2 * c1)] += 1
        print('  dQ profile :', dict(sorted(dqs.items())))
        print('  sum dQ =', (tr[-1][1] + 2 * tr[-1][2]) - (tr[0][1] + 2 * tr[0][2]) if tr else 0)

if __name__ == '__main__':
    main()
