"""Print the window trace of a candidate rule, to find its phase decomposition."""
from winchk import lstep, U, V, u

def trace(q, k, l, maxn=100000):
    n = 0
    out = []
    while n < maxn:
        s = ''.join(str(x) for x in l)
        out.append('%4d  %s%s%s  %s' % (n, s[:k], '[' + q + ']', s[k:], ''))
        r = lstep(q, k, l)
        if r is None:
            break
        q, k, l = r
        n += 1
    return out

if __name__ == '__main__':
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else 'P1'
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    if which == 'P1':
        l = [0, 0, 0] + U(2, 1) + U(4, 1) + U(1, 2*m) + [0]
    else:
        l = [0, 0, 0] + U(2, 2) + V(1) + u + U(1, 2*m) + [0]
    for ln in trace('B', 3, l):
        print(ln)
