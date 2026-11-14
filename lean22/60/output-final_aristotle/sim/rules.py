from sim import T
import collections
def parse(w):
    i=0; out=[]
    while i<len(w):
        if w[i]==0:
            j=i+1; a=0
            while j<len(w) and w[j]==4: a+=1; j+=1
            b=0
            while j<len(w) and w[j]==2: b+=1; j+=1
            out.append(('U',a,b)); i=j
        elif i+1<len(w) and w[i]==4 and w[i+1]==3:
            j=i+2; c=0
            while j<len(w) and w[j]==2: c+=1; j+=1
            out.append(('V',c)); i=j
        else: return None
    return out
def f1(t):
    if t[0]=='U': return 'u' if t[1:]==(1,1) else 'U%s,%s'%(t[1],t[2])
    return 'V%s'%t[1]
# simulate real machine, sync at state B on new leftmost cell
tape=collections.defaultdict(int); pos=0; st='A'; t=0; minpos=0
events=[]
LIM=3000000
prev=None
while t<LIM:
    r=T[(st,tape[pos])]
    if r is None: break
    w,d,ns=r; tape[pos]=w; pos+=d; st=ns; t+=1
    if pos<minpos:
        minpos=pos
        if st=='B':
            ks=[k for k,v in tape.items() if v!=0]
            hi=max(ks)
            word=[tape[i] for i in range(pos,hi+1)]
            p=parse(word)
            events.append((t,pos,p))
# now for each consecutive pair compute rule
rules=collections.Counter()
for (t1,p1,W1),(t2,p2,W2) in zip(events,events[1:]):
    # find max head pos between t1 and t2 -> recompute? instead compare words
    k=0
    while k<min(len(W1),len(W2)) and False: pass
    # changed prefix: find smallest k such that W1[k:] == W2[k+delta:]
    found=None
    for delta in range(-3,4):
        for k in range(0,min(len(W1),len(W2))+1):
            if k+delta>=0 and W1[k:]==W2[k+delta:]:
                found=(k,delta); break
        if found: break
    if found:
        k,delta=found
        rules[(tuple(f1(x) for x in W1[:k]), tuple(f1(x) for x in W2[:k+delta]))]+=1
    else:
        rules[('??','??')]+=1
print('num events',len(events),'num distinct rules',len(rules))
for (a,b),c in rules.most_common(40):
    print('%6d  %-45s  ==>  %s'%(c,' '.join(a) if a!='??' else a,' '.join(b) if b!='??' else b))
