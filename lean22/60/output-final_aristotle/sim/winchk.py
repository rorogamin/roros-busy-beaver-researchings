"""Check candidate window rules (the `Win` predicate of RequestProject/Local.lean)
by list-level simulation that refuses to leave the window."""
from sim import T

def lstep(q, k, l):
    if not (0 <= k < len(l)):
        return None
    v = l[k]
    r = T.get((q, v))
    if r is None:
        return None
    w, d, s = r
    l2 = list(l); l2[k] = w
    k2 = k + d
    if not (0 <= k2 < len(l)):
        return None
    return (s, k2, l2)

def lrun(q, k, l, maxn=100000):
    """run until the head would leave the window; return (n, q, k, l)"""
    n = 0
    while n < maxn:
        r = lstep(q, k, l)
        if r is None:
            return (n, q, k, l)
        q, k, l = r
        n += 1
    return None

def U(a, b): return [0] + [4]*a + [2]*b
def V(c): return [4, 3] + [2]*c
u = U(1, 1)

def show(name, q, k, l):
    r = lrun(q, k, l)
    print('%-22s in  %s @%d %s' % (name, ''.join(map(str, l)), k, q))
    print('%-22s out %s @%d %s  after %d steps' %
          ('', ''.join(map(str, r[3])), r[2], r[1], r[0]))

if __name__ == '__main__':
    for m in range(1, 6):
        show('P1 m=%d' % m, 'B', 3, [0, 0, 0] + U(2, 1) + U(4, 1) + U(1, 2*m) + [0])
    for m in range(1, 6):
        show('P3 m=%d' % m, 'B', 3, [0, 0, 0] + U(2, 2) + V(1) + u + U(1, 2*m) + [0])
    show('P2', 'B', 3, [0, 0, 0] + U(2, 2) + [0])
