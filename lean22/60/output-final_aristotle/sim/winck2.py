"""Check a candidate window rule: run the window simulator (which refuses to let the head
leave the window) from (q, k, l) and compare with (q', k', l') after n steps."""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

def lrun(q, k, l, n):
    l = list(l)
    for _ in range(n):
        if not (0 <= k < len(l)): return None
        r = T[(q, l[k])]
        if r is None: return None
        w, d, s = r
        l[k] = w; k += d; q = s
        if not (0 <= k < len(l)): return None
    return q, k, l

def check(q, k, l, n, q2, k2, l2):
    res = lrun(q, k, l, n)
    if res is None: return 'escape/halt'
    if res == (q2, k2, list(l2)): return 'ok'
    return 'MISMATCH got %s' % (res,)

def find(q, k, l, stop):
    """run until stop(q,k,l) or escape; return (n,q,k,l)"""
    l = list(l); n = 0
    while True:
        if stop(q, k, l): return n, q, k, l
        if not (0 <= k < len(l)): return None
        r = T[(q, l[k])]
        if r is None: return None
        w, d, s = r
        l[k] = w; k += d; q = s; n += 1
        if n > 10**6: return None
