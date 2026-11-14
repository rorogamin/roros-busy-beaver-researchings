from sim import M
import itertools,re
def tokenize(w):
    # split into tokens starting at each '0'
    toks=[]; cur=''
    for ch in w:
        if ch=='0' and cur: toks.append(cur); cur='0'
        else: cur+=ch
    if cur: toks.append(cur)
    return toks
def rle(w):
    return ''.join(('%s^%d'%(c,len(list(g))) if len(list2:=list(g))>1 or True else c) for c,g in itertools.groupby(w))
def comp(toks):
    out=[];  # compress repeats of same token
    for t,g in itertools.groupby(toks):
        n=len(list(g))
        out.append(t if n==1 else '(%s)^%d'%(t,n))
    return ' '.join(out)
m=M(); minpos=0; n=0
while m.t<400000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%9==1:
            lo,w=m.word()
            w=w.replace('[B]','').replace('[A]','')
            print(n,'t=%d'%m.t, comp(tokenize(w))[:300])
        n+=1
