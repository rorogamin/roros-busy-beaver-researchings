from sim import M
import itertools,re
def tokenize(w):
    toks=[]; cur=''
    for ch in w:
        if ch=='0' and cur: toks.append(cur); cur='0'
        else: cur+=ch
    if cur: toks.append(cur)
    return toks
def enc(toks):
    out=[]; run=0
    for t in toks:
        if t=='042': run+=1
        else:
            out.append(run); out.append(t); run=0
    out.append(run)
    return out
m=M(); minpos=0; n=0
while m.t<1500000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%9==1:
            lo,w=m.word()
            w=w.replace('[B]','').replace('[A]','')
            e=enc(tokenize(w))
            nspec=(len(e)-1)//2
            print('%5d t=%-9d ns=%d'%(n,m.t,nspec), ' '.join(map(str,e)))
        n+=1
