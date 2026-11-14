import random
exec(open('closure.py').read().split('random.seed')[0])
def stepW(toks,maxsteps=50000000):
    r=run(toks,maxsteps)
    return r
def f1(t):
    if t[0]=='U': return 'u' if t[1:]==(1,1) else 'U%d,%d'%(t[1],t[2])
    return 'V%d'%t[1]
def fmt(ts):
    s=[f1(t) for t in ts]; out=[];i=0
    while i<len(s):
        j=i
        while j<len(s) and s[j]==s[i]: j+=1
        out.append(s[i] if j-i==1 else '%s^%d'%(s[i],j-i)); i=j
    return ' '.join(out)
tests=[
 [('U',2,1),('U',4,1),('U',1,4),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,6),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,8),('U',1,1)],
 [('U',2,1),('U',4,1),('U',2,4),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,4),('V',5),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,10),('V',9),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,10),('V',9),('U',1,1),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,1),('U',1,1),('U',2,2),('V',1),('U',1,1)],
 [('U',2,1),('U',4,1),('U',1,1),('U',1,1),('U',1,1),('U',2,6),('V',3),('U',1,1),('U',1,1)],
]
for t in tests:
    r=stepW(t)
    print(fmt(t),'  ==>  ', r[0], fmt(r[1]) if r[0]=='OK' else r[1])
