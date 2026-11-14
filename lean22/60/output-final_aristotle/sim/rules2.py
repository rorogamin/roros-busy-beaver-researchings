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
    return ('u' if t[1:]==(1,1) else 'U%s,%s'%(t[1],t[2])) if t[0]=='U' else 'V%s'%t[1]
def fs(ts): return ' '.join(f1(t) for t in ts)
def wlen(t): return 1+t[1]+t[2] if t[0]=='U' else 2+t[1]
# simulate; at each sync record tape word; then recompute the excursion to find hi
tape=collections.defaultdict(int); pos=0; st='A'; t=0; minpos=0
events=[]
while t<600000:
    r=T[(st,tape[pos])]
    if r is None: break
    w,d,ns=r; tape[pos]=w; pos+=d; st=ns; t+=1
    if pos<minpos:
        minpos=pos
        if st=='B':
            hi=max(k for k,v in tape.items() if v!=0)
            events.append((t,pos,[tape[i] for i in range(pos,hi+1)]))
rules=collections.Counter()
for (t1,p1,W1),(t2,p2,W2) in zip(events,events[1:]):
    # rerun from W1 to find max head reach
    tp={i:v for i,v in enumerate(W1)}
    p=0; s='B'; n=0; hi=0
    while True:
        r=T[(s,tp.get(p,0))]
        w,d,ns=r; tp[p]=w; p+=d; s=ns; n+=1; hi=max(hi,p)
        if p==-3 and s=='B': break
    tin=parse(W1); 
    # tokens covering cells 0..hi
    c=0; k=0
    while c<=hi and k<len(tin): c+=wlen(tin[k]); k+=1
    inp=tin[:k]
    # output tokens covering the same region: output cells -3..(c-1)
    out=parse([tp.get(i,0) for i in range(-3,c)])
    rules[(fs(inp),fs(out) if out else '??',n)]+=1
print(len(rules))
for (a,b,n),c in sorted(rules.items(), key=lambda x:-x[1])[:45]:
    print('%5d  n=%-5d %-40s ==> %s'%(c,n,a,b))
