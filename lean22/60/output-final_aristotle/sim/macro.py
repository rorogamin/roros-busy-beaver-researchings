"""RLE macro-simulator with chain steps."""
T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}
class Cfg:
    def __init__(s):
        s.L=[(0,None)]; s.R=[(0,None)]; s.c=0; s.st='A'; s.t=0
    def copy(s):
        c=Cfg.__new__(Cfg); c.L=list(s.L); c.R=list(s.R); c.c=s.c; c.st=s.st; c.t=s.t; return c
    def show(s,maxn=40):
        def f(l,rev):
            it = l if not rev else reversed(l)
            return ' '.join('%d^%s'%(a,'w' if n is None else n) for a,n in it)
        return '%s [%s%d] %s'%(f(s.L,False), s.st, s.c, f(s.R,True))
    def key(s):
        return (tuple(a for a,n in s.L), s.st, s.c, tuple(a for a,n in s.R))
    def exps(s):
        return tuple((n if n is not None else -1) for a,n in s.L)+tuple((n if n is not None else -1) for a,n in s.R)

def push(st,sym,n):
    if n==0: return
    if st and st[-1][0]==sym:
        if st[-1][1] is None or n is None: st[-1]=(sym,None)
        else: st[-1]=(sym,st[-1][1]+n)
    else: st.append((sym,n))

def pop1(st):
    sym,n=st[-1]
    if n is None: return sym
    if n==1: st.pop()
    else: st[-1]=(sym,n-1)
    return sym

def popall(st,sym):
    """pop the whole top run if its symbol is sym; return count (None if infinite)"""
    s,n=st[-1]
    assert s==sym
    if n is None: return None
    st.pop(); return n

def step(c):
    tr=T[(c.st,c.c)]
    if tr is None: return 'HALT'
    w,d,q=tr
    src = c.R if d>0 else c.L
    dst = c.L if d>0 else c.R
    if q==c.st and src[-1][0]==c.c:
        n=popall(src,c.c)
        if n is None: return 'INF'
        push(dst,w,n+1)
        c.c = pop1(src)
        c.t += n+1
        return True
    push(dst,w,1)
    c.c = pop1(src)
    c.st=q; c.t+=1
    return True
