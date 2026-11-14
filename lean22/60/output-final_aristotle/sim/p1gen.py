"""Window-simulate the P1 rule with r intervening u tokens, to find the general form."""
import sys
from sim import T
from toklib import parse, fmt


def lrun(q, k, l, maxn=200000):
    """window simulator: refuses to leave the window; returns (q,k,l,n) at first
    moment the head is back in state B at offset 0."""
    l = [int(c) for c in l]
    n = 0
    while n < maxn:
        if not (0 <= k < len(l)):
            return ('OUT', n, q, k, l)
        r = T[(q, l[k])]
        if r is None:
            return ('HALT', n, q, k, l)
        w, d, s = r
        l[k] = w
        k += d
        q = s
        n += 1
        if q == 'B' and k == 0:
            return ('DONE', n, q, k, l)
    return ('TIME', n, q, k, l)


def U(a, b): return '0' + '4' * a + '2' * b


if __name__ == '__main__':
    for m in range(0, 3):
        for r in range(0, 5):
            w = '000' + U(2, 1) + U(4, 1) + U(1, 1) * r + U(1, 2 * m + 2) + '0'
            res = lrun('B', 3, w)
            print('r=%d m=%d  %-6s n=%-6d  %s   -> %s' %
                  (r, m, res[0], res[1], w, ''.join(map(str,res[4]))))
            if res[0] == 'DONE':
                print('        tokens: %s' % fmt(parse(''.join(map(str,res[4]))[:-1])))
