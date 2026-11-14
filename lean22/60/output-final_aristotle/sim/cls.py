from sim import M
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
            out.append(('?',w[i])); i+=1
    return out
m=M(); minpos=0; n=0
bad=0; Us=set(); Vs=set(); pairs=set(); firsts=set(); lasts=set()
while m.t<8000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        lo,w=m.word()
        w=w.replace('[B]','').replace('[A]','')
        if n%3==1:
            t=parse(w)
            if any(x[0]=='?' for x in t): bad+=1; print('BAD',w[:60]); break
            for x in t:
                if x[0]=='U': Us.add(x[1:])
                else: Vs.add(x[1])
            for x,y in zip(t,t[1:]):
                pairs.add((x[0],y[0]))
            firsts.add(t[0]); lasts.add(t[-1])
        n+=1
print('events',n,'bad',bad)
print('pairs',pairs)
print('#U',len(Us),'a-range',sorted(set(a for a,b in Us))[:20],'...')
print('b-range',sorted(set(b for a,b in Us))[:20])
print('Vs',sorted(Vs)[:30], 'max',max(Vs))
print('firsts',sorted(firsts))
print('lasts',sorted(lasts)[:10])
# U with b==0?
print('b=0 Us',[u for u in Us if u[1]==0][:10])
print('a=0 Us',[u for u in Us if u[0]==0][:10])
