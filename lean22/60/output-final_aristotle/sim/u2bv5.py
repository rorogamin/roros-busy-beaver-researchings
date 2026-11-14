"""Dump the six fixed stretches of the `P3`/`U(2,8)`/`V` row (cells 0..28)."""
from u21b import T
from u2bv2 import word, out
from u2bv4 import stages

def dump(t, m):
    l = list(word(t, m)); q, k = 'B', 3
    for (nm, n, qq, kk) in stages(t, m):
        before = ''.join(map(str, l[0:29]))
        q0, k0 = q, k
        mx = k
        for _ in range(n):
            w, d, s = T[(q, l[k])]
            l[k] = w; k += d; q = s
            mx = max(mx, k)
        if 'fixed' in nm or 'open' in nm or 'close' in nm:
            print('%-14s %s%-3d -> %s%-3d  %3d steps  max cell %d' % (nm, q0, k0, q, k, n, mx))
            print('  in : %s' % before)
            print('  out: %s' % ''.join(map(str, l[0:29])))

dump(3, 2)
