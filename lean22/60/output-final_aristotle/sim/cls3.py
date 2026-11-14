exec(open('fit.py').read().split('tests=')[0])
import random, collections
def inclass(toks):
    if not toks: return False
    if toks[0][0]!='U': return False
    if not (toks[-1][0]=='U' and toks[-1][2]==1): return False
    for i,t in enumerate(toks):
        nx = toks[i+1] if i+1<len(toks) else None
        if t[0]=='U':
            a,b=t[1],t[2]
            if a<1 or b<1: return False
            if b>=2 and (a>2 or b%2==1): return False
            if a>=3 and b!=1: return False
            if a==2 and b==2 and (nx is None or nx[0]!='V'): return False
        else:
            c=t[1]
            if c<1 or c%2==0: return False
            if i==0 or toks[i-1][0]!='U' or toks[i-1][2]<2: return False
            if nx is None or nx!=('U',1,1): return False
    return True
def gen(maxm=7,amax=2):
    while True:
        toks=[]
        while len(toks)<random.randint(1,maxm):
            r=random.random()
            if r<0.4: toks.append(('U',random.choice([1,2] if amax==2 else [1,2,4,10,28]),1))
            elif r<0.7: toks.append(('U',random.choice([1,2]),2*random.randint(2,7)))
            else:
                toks.append(('U',random.choice([1,2]),2*random.randint(1,7)))
                toks.append(('V',2*random.randint(0,7)+1)); toks.append(('U',1,1))
        toks.append(('U',1,1))
        if inclass(toks): return toks
prefs={'P1':[('U',2,1),('U',4,1)],'P2':[('U',2,2),('U',1,1)],'P3':[('U',2,2),('V',1),('U',1,1)]}
random.seed(5)
st=collections.Counter(); ex=collections.defaultdict(list)
for _ in range(250):
    R=gen()
    for k,p in prefs.items():
        W=p+R
        r=run(W,20000000)
        if r[0]!='OK': st[(k,r[0])]+=1; ex[k].append((fmt(R),r[:2]))
        elif not inclass(r[1]): st[(k,'OUTCLASS')]+=1; ex[k+'oc'].append((fmt(R),fmt(r[1])))
        else: st[(k,'OK')]+=1
print(st)
for k in ex:
    for e in ex[k][:3]: print(k,e)
