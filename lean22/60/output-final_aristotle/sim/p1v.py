"""The `P1` macro step in which a token `V` follows the token the carry reaches.

Exploratory only; nothing here is machine-checked.
"""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

def U(a,b): return [0]+[4]*a+[2]*b
def V(c):   return [4,3]+[2]*c
u = U(1,1)

def word(m,c,s,mp):
    return ([0,0,0] + U(2,1) + U(4,1) + U(1,2*m+2) + V(2*c+5) + u*s + U(1,2*mp+2) + [0])

def out(m,c,s,mp):
    return (U(2,2) + u + U(2,2*m+6) + V(2*c+1) + u*s + U(1,2*mp+6) + [0])

def steps(m,c,s,mp):
    return 171 + 20*m + 20*c + 12*s + 20*mp

def run(q,k,l,n):
    l=list(l)
    for _ in range(n):
        if not (0<=k<len(l)): return None
        t=T[(q,l[k])]
        if t is None: return None
        w,d,s=t; l[k]=w; k+=d; q=s
    if not (0<=k<len(l)): return None
    return q,k,l

def trace(q,k,l,n):
    l=list(l); res=[(q,k,list(l))]
    for _ in range(n):
        t=T[(q,l[k])]
        w,d,s=t; l[k]=w; k+=d; q=s
        res.append((q,k,list(l)))
    return res

def to_b0(l, k=3, q='B', limit=10**5):
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

if __name__ == '__main__':
    bad = 0
    for m in range(3):
        for c in range(3):
            for s in range(3):
                for mp in range(3):
                    res = to_b0(word(m,c,s,mp))
                    exp = (steps(m,c,s,mp), out(m,c,s,mp))
                    if res != exp:
                        bad += 1
                        if bad < 4:
                            print('MISMATCH', m, c, s, mp)
                            print('  got', res[0] if res else None,
                                  ''.join(map(str,res[1])) if res else '')
                            print('  exp', exp[0], ''.join(map(str,exp[1])))
    print('mismatches:', bad)
