from sim import T
def word_of(toks):
    s=[]
    for t in toks:
        if t[0]=='U': s+= [0]+[4]*t[1]+[2]*t[2]
        else: s+=[4,3]+[2]*t[1]
    return s
def analyze(toks,tailpad=40):
    w=word_of(toks)
    tape={}
    for i,v in enumerate(w): tape[i]=v
    pos=0; st='B'; lo=0; hi=0; t=0
    while True:
        r=T[(st,tape.get(pos,0))]
        if r is None: return ('HALT',t)
        wr,d,ns=r; tape[pos]=wr; pos+=d; st=ns; t+=1
        lo=min(lo,pos); hi=max(hi,pos)
        if pos==-3 and st=='B': break
        if t>10**7: return ('TIMEOUT',)
    out=[tape.get(i,0) for i in range(-3,hi+2)]
    return ('OK',t,lo,hi,len(w),out)
def show(toks):
    r=analyze(toks)
    print(toks, '->', r[0], 'steps=%s hi=%s wlen=%s'%(r[1],r[4-1] if False else r[3],r[4]) if r[0]=='OK' else '')
    if r[0]=='OK': print('   window[-3..hi+1]:',''.join(map(str,r[5])))
P1=[('U',2,1),('U',4,1)]
P3=[('U',2,2),('V',1),('U',1,1)]
for b in (2,4,6,8):
    show(P1+[('U',1,b),('U',1,1),('U',1,1)])
for b in (2,4,6,8):
    show(P3+[('U',1,b),('U',1,1),('U',1,1)])
