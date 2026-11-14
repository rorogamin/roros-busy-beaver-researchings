from sim import M
exec(open('closure.py').read().split('def valid')[0].split('import random')[1])
m=M(); minpos=0; n=0
afterV=set(); beforeV=set(); last=set(); first2=set(); allU=set()
while m.t<8000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if n%3==1:
            lo,w=m.word(); t=parse(w.replace('[B]','').replace('[A]',''))
            for i,x in enumerate(t):
                if x[0]=='V':
                    beforeV.add(t[i-1]); afterV.add(t[i+1] if i+1<len(t) else 'END')
            last.add(t[-1]); first2.add(tuple(t[:2]))
            for x in t:
                if x[0]=='U': allU.add(x[1:])
        n+=1
print('beforeV b-values:',sorted(set(x[2] for x in beforeV)))
print('beforeV a-values:',sorted(set(x[1] for x in beforeV)))
print('afterV:',sorted(set(x if x=='END' else x[:3] for x in afterV))[:20])
print('last:',sorted(last))
print('first2:',sorted(first2))
print('U (a,b) pairs sample:',sorted(allU)[:40])
