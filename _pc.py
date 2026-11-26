from _ph import trace, phases
best={}
rows=[]
for k in list(range(1,26))+[50,100,150,200,250,280,288,289,290,291,292]:
    top=2*3**k
    cls=list(range(1,min(top,200)))+[top//2,top//3,top//7,top-1,top-2,2047,2052]
    for c0v in cls:
        if not (1<=c0v<top): continue
        seq=trace(k,c0v); ph=phases(seq)
        tot=len(seq)
        # phases starting at step >= 791 (residual part)
        res=[p for p in ph if p[4]>=791]
        nL=sum(1 for p in res if p[2]=='L'); nJ=len(res)-nL
        totL=sum(p[3] for p in res if p[2]=='L'); totJ=sum(p[3] for p in res if p[2]=='J')
        rows.append((k,c0v,tot,len(ph),len(res),nL,nJ,totL,totJ,max([p[3] for p in res],default=0)))
rows.sort(key=lambda r:-r[3])
print("worst by total phases: k c0 totlen nph nph_res nL nJ lenL lenJ maxphase")
for r in rows[:8]: print(r)
rows.sort(key=lambda r:-r[4])
for r in rows[:8]: print(r)
print("max nph_res", max(r[4] for r in rows), "max nL_res", max(r[5] for r in rows), "max totlen", max(r[2] for r in rows))
import collections
print("nph_res hist", sorted(collections.Counter(r[4] for r in rows).items()))
