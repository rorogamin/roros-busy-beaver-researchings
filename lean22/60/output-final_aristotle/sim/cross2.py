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
        if len(t)<12: break
        for r in range(6):
            if all(t[j]==per[(r+j)%6] for j in range(len(t))): return k,s[:k],r
    return None
c=crossings(4000000)
for i in range(1,-61,-1):
    if i in c:
        p=prefix(c[i])
        if p: print(i,'len=%d tlen=%d r=%d'%(len(c[i]),p[0],p[2]),p[1])
        else: print(i,'len=%d NOPER'%len(c[i]), c[i][:80])
