from sim import M
exec(open('closure.py').read().split('def valid')[0].split('import random')[1])
m=M(); minpos=0; n=0
import collections
pairs=collections.Counter(); after=collections.Counter()
Ua1=collections.Counter()
while m.t<8000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%3==1:
            lo,w=m.word(); t=parse(w.replace('[B]','').replace('[A]',''))
            for i,x in enumerate(t):
                if x[0]=='V':
                    pv=t[i-1]
                    pairs[(pv[1], 'b>=4' if pv[2]>=4 else 'b=%d'%pv[2], 'c=1' if x[1]==1 else 'c>1')]+=1
                if x[0]=='U' and x[1]>=3:
                    # count following u's
                    j=i+1; c=0
                    while j<len(t) and t[j]==('U',1,1): c+=1; j+=1
                    nxt = t[j] if j<len(t) else None
                    Ua1[(x[1], c, None if nxt is None else (nxt[0],nxt[1] if nxt[0]=='V' else nxt[1]))]+=1
            n2=0
        n+=1
print('U(a,b) V(c) combos:')
for k,v in sorted(pairs.items()): print('  ',k,v)
print('U(a,1) with a>=3: (a, #following u, next token)')
for k,v in sorted(Ua1.items(), key=lambda x: (x[0][0],x[0][1],str(x[0][2]))): print('  ',k,v)
