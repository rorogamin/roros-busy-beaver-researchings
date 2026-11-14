from sim import M
import re
def parse(w):
    """parse into tokens U(a,b)='0'+'4'*a+'2'*b  and V(c)='43'+'2'*c"""
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
def fmt(toks):
    s=[]
    for t in toks:
        if t[0]=='U': s.append('u' if t[1:]==(1,1) else 'U%d,%d'%(t[1],t[2]))
        elif t[0]=='V': s.append('V%d'%t[1])
        else: s.append('?'+t[1])
    # compress runs of u
    out=[];i=0
    while i<len(s):
        j=i
        while j<len(s) and s[j]==s[i]: j+=1
        out.append(s[i] if j-i==1 else '%s^%d'%(s[i],j-i)); i=j
    return ' '.join(out)
m=M(); minpos=0; n=0
while m.t<40000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        lo,w=m.word()
        w=w.replace('[B]','').replace('[A]','')
        if True:
            print('%4d t=%-8d'%(n,m.t), fmt(parse(w)))
        n+=1
