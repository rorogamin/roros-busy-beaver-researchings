import random
from sim import T
def word_of(toks):
    s=''
    for t in toks:
        if t[0]=='U': s+='0'+'4'*t[1]+'2'*t[2]
        else: s+='43'+'2'*t[1]
    return s
def parse(w):
    i=0; out=[]
    while i<len(w):
        if w[i]=='0':
            j=i+1; a=0
            while j<len(w) and w[j]=='4': a+=1; j+=1
            b=0
            while j<len(w) and w[j]=='2': b+=1; j+=1
            out.append(('U',a,b)); i=j
        elif w[i:i+2]=='43':
            j=i+2; c=0
            while j<len(w) and w[j]=='2': c+=1; j+=1
            out.append(('V',c)); i=j
        else:
            return None
    return out
def valid(toks):
    if not toks: return False
    if toks[0][0]!='U': return False
    for t in toks:
        if t[0]=='U' and (t[1]<1 or t[2]<1): return False
        if t[0]=='V' and t[1]<1: return False
    for x,y in zip(toks,toks[1:]):
        if x[0]=='V' and y[0]=='V': return False
    return True

def run(toks, maxsteps=100000000):
    w=word_of(toks)
    tape={}
    for i,ch in enumerate(w): tape[i]=int(ch)
    pos=0; st='B'; t=0
    minpos=0
    while True:
        r=T[(st,tape.get(pos,0))]
        if r is None: return ('HALT',t)
        wr,d,ns=r; tape[pos]=wr; pos+=d; st=ns; t+=1
        if t>maxsteps: return ('TIMEOUT',t)
        if pos<minpos:
            minpos=pos
            if pos==-3:
                # check config
                if st!='B': return ('STATE',st,t)
                ks=[k for k,v in tape.items() if v!=0]
                hi=max(ks) if ks else pos
                s=''.join(str(tape.get(i,0)) for i in range(pos,hi+1))
                p=parse(s)
                if p is None: return ('UNPARSE',s[:80],t)
                if not valid(p): return ('INVALID',p[:6],t)
                return ('OK',p,t)

random.seed(1)
fails=0
for trial in range(300):
    m=random.randint(1,6)
    toks=[]
    prevV=False
    for i in range(m):
        if not prevV and i>0 and random.random()<0.3:
            toks.append(('V',random.randint(1,8))); prevV=True
        else:
            toks.append(('U',random.randint(1,5),random.randint(1,8))); prevV=False
    if toks[-1][0]=='V': toks.append(('U',1,1))
    if toks[0][0]!='U': continue
    res=run(toks,2000000)
    if res[0]!='OK':
        fails+=1
        if fails<10: print('FAIL',toks,res[:2])
print('fails',fails,'/300')
