from sim import M
import re
def strip042(w):
    while w.endswith('042'): w=w[:-3]
    return w
m=M(); minpos=0; n=0
W={}
while m.t<3000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        lo,w=m.word()
        w=w.replace('[B]','').replace('[A]','')
        W[n]=w
        n+=1
print('events',n)
def lcp(a,b):
    i=0
    while i<min(len(a),len(b)) and a[i]==b[i]: i+=1
    return i
# check nesting within residue classes mod P
for P in (9,13,117,39):
    ok=0; bad=0
    for r in range(P):
        idx=[i for i in range(1,n) if i%P==r]
        for a,b in zip(idx,idx[1:]):
            sa=strip042(W[a]); 
            if W[b].startswith(sa): ok+=1
            else: bad+=1
    print('P=%d ok=%d bad=%d'%(P,ok,bad))

def lcp2(a,b):
    i=0
    while i<min(len(a),len(b)) and a[i]==b[i]: i+=1
    return i
for d in (9,117,234):
    print('d=%d'%d, [(i,len(W[i]),lcp2(W[i],W[i+d])) for i in range(1,60,9) if i+d<n])
