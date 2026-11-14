"""Explore the general 'flat' P3 macro step: prefix U(2,2)V(1)u, then an arbitrary
sequence of blocks 0 4^a 2 with a in {1,2}, then the absorbing token U(1,2m+2), then 0.

Runs the window simulator (head must stay inside the window) from state B at offset 3
until it returns to offset 0 in state B, and prints the resulting word and step count.
"""
import sys

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

def blocks(js):
    w = []
    for a in js:
        w += [0] + [4]*a + [2]
    return w

def run(word, k=3, st='B', limit=10**7):
    l = list(word); n = 0
    while True:
        if not (0 <= k < len(l)): return ('escape', n, k, l)
        r = T[(st, l[k])]
        if r is None: return ('halt', n, k, l)
        w, d, s = r
        l[k] = w; k += d; st = s; n += 1
        if st == 'B' and k == 0:
            return ('done', n, k, l)
        if n > limit: return ('timeout', n, k, l)

def fmt(l):
    return ''.join(str(x) for x in l)

def tokens(l):
    from toklib import parse, fmt as tf
    return tf(parse(fmt(l)))

if __name__ == '__main__':
    import itertools
    # total block list is 1^(r+1) ++ [2] ++ ks
    bad = 0
    for r in range(3):
        for L in range(4):
            for ks in itertools.product([1,2], repeat=L):
                ks = list(ks)
                for m in [0,1,2]:
                    js = [1]*r + [2] + ks
                    word = ([0,0,0] + [0,4,4,2,2] + [4,3,2] + [0,4,2] + blocks(js)
                            + [0,4] + [2]*(2*m+2) + [0])
                    res, n, k, l = run(word)
                    # predicted output word
                    out = ([0,4,4,2] + [0,4,4,4,4,2] + [0,4,2]*r + [0,4,2,2,2,2]
                           + sum(([0,4]+[2]*x for x in ks), []) + [0,4] + [2]*(2*m+4) + [0])
                    cost = 91 + 12*r + 10*m + sum(4*x+2 for x in ks)
                    ok = (res == 'done' and n == cost and l == out)
                    if not ok:
                        bad += 1
                        print('MISMATCH r=%d ks=%s m=%d: res=%s n=%d (pred %d)' % (r, ks, m, res, n, cost))
                        print('   got  %s' % fmt(l))
                        print('   pred %s' % fmt(out))
    print('done, mismatches =', bad)
