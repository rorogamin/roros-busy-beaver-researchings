"""Probe the macro step whose absorbing token is `U(2,b)` and which is followed by a `V`.

Exploratory only; nothing here is machine-checked.
"""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

def U(a,b): return [0]+[4]*a+[2]*b
def V(c):   return [4,3]+[2]*c
u = U(1,1)

def word(r,m,c,s,mp):
    return ([0,0,0] + U(2,2) + V(1) + u + u*r + U(2,2*m+4) + V(2*c+5)
            + u*s + U(1,2*mp+2) + [0])

def to_b0(l, k=3, q='B', limit=10**6):
    """run until the head is at position 0 in state B; return (steps, tape)."""
    l = list(l); n = 0
    while n < limit:
        if k == 0 and q == 'B':
            return n, l
        if not (0 <= k < len(l)): return None
        t = T[(q, l[k])]
        if t is None: return None
        w, d, s = t
        l[k] = w; k += d; q = s; n += 1
    return None

def show(r,m,c,s,mp):
    res = to_b0(word(r,m,c,s,mp))
    if res is None:
        print(r,m,c,s,mp,'escape/halt')
        return None
    n, l = res
    print(r,m,c,s,mp,n,''.join(map(str,l)))
    return n, l

if __name__ == '__main__':
    for (r,m,c,s,mp) in [(0,0,0,0,0),(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0),
                         (0,0,0,1,0),(0,0,0,0,1),(1,1,1,1,1)]:
        show(r,m,c,s,mp)
