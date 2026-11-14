from sim import M
exec(open('closure.py').read().split('def valid')[0].split('import random')[1])
def fmt1(t):
    if t[0]=='U': return 'u' if t[1:]==(1,1) else 'U%d,%d'%(t[1],t[2])
    return 'V%d'%t[1]
def fmt(ts):
    s=[fmt1(t) for t in ts]; out=[];i=0
    while i<len(s):
        j=i
        while j<len(s) and s[j]==s[i]: j+=1
        out.append(s[i] if j-i==1 else '%s^%d'%(s[i],j-i)); i=j
    return ' '.join(out)
m=M(); minpos=0; n=0; Ws=[]
while m.t<200000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%3==1:
            lo,w=m.word(); w=w.replace('[B]','').replace('[A]','')
            Ws.append((n,parse(w)))
        n+=1
for (n1,a),(n2,b) in zip(Ws,Ws[1:]):
    # common prefix / suffix
    p=0
    while p<min(len(a),len(b)) and a[p]==b[p]: p+=1
    s=0
    while s<min(len(a),len(b))-p and a[len(a)-1-s]==b[len(b)-1-s]: s+=1
    print('%4d->%4d  pre=%d suf=%d | %s   ==>   %s'%(n1,n2,p,s,fmt(a[p:len(a)-s]),fmt(b[p:len(b)-s])))
