"""Trace the macro step in which a token `V` follows the absorbing token
(ANALYSIS.md §32, row 2).  Exploratory only; nothing here is machine-checked."""

T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

def U(a,b): return [0]+[4]*a+[2]*b
def V(c):   return [4,3]+[2]*c
u = U(1,1)

def word(r,m,c,s,mp):
    return ([0,0,0] + U(2,2) + V(1) + u + u*(r+1) + U(1,2*m+2) + V(2*c+5)
            + u*s + U(1,2*mp+2) + [0])

def out(r,m,c,s,mp):
    return (U(2,1) + U(4,1) + u*(r+1) + U(1,2*m+6) + V(2*c+1)
            + u*s + U(1,2*mp+6) + [0])

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

def steps(r,m,c,s,mp):
    return 195+12*r+20*m+20*c+12*s+20*mp

if __name__ == '__main__':
    bad = 0
    for r in range(3):
        for m in range(3):
            for c in range(3):
                for s in range(3):
                    for mp in range(3):
                        res = run('B', 3, word(r, m, c, s, mp), steps(r, m, c, s, mp))
                        if res != ('B', 0, out(r, m, c, s, mp)):
                            bad += 1
                            if bad < 4:
                                print('MISMATCH', r, m, c, s, mp, res)
    print('mismatches:', bad)
