from sim import M
import itertools,re
def rle(w):
    out=[]
    for ch,g in itertools.groupby(w):
        n=len(list(g)); out.append((ch,n))
    return out
def fmt(r):
    return ' '.join('%s^%d'%(c,n) if n>1 else c for c,n in r)
m=M(); minpos=0; n=0
while m.t<3000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%3==1:
            lo,w=m.word()
            w=w.replace('[B]','').replace('[A]','')
            r=rle(w)
            print(n,'t=%d ntok=%d'%(m.t,len(r)), fmt(r) if len(r)<60 else '...')
        n+=1
