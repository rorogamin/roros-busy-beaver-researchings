from sim import M
m=M(); minpos=0; n=0
W=[]
while m.t<20000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        lo,w=m.word()
        W.append(w.replace('[B]','').replace('[A]',''))
print('events',len(W))
N=len(W)
for d in (81,243,729,2187):
    ok=sum(1 for i in range(N-d) if W[i+d].startswith(W[i]))
    print('d=%d: prefix-ok %d / %d'%(d,ok,N-d))
