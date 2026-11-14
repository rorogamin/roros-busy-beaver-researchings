from sim import M
per='AAABBB'
def crossings(N):
    m=M(); cross={}
    while m.t<N:
        p0=m.pos; m.step(); p1=m.pos
        if p1>p0: cross.setdefault(p1,[]).append(m.st)
        else: cross.setdefault(p0,[]).append(m.st)
    return {k:''.join(v) for k,v in cross.items()}
def prefix(s):
    for k in range(len(s)):
        t=s[k:]
        for r in range(6):
            if all(t[j]==per[(r+j)%6] for j in range(len(t))): return k,s[:k],r
    return len(s),s,None
if __name__=='__main__':
    import sys
    for N in (500000,2000000,8000000):
        c=crossings(N)
        out=[]
        for i in (-40,-30,-20,-10,0,1,5):
            if i in c:
                k,p,r=prefix(c[i]); out.append('%d:len=%d,pref=%d'%(i,len(c[i]),k))
        print(N, ' | '.join(out))
