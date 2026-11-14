import sys,bisect
T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
 ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
N=20000; tape=[0]*N; pos=N//2; st='A'; lo=hi=pos; steps=0
LIMIT=int(sys.argv[1])
events=[]; m=None; fronts=[]; snaps={}
while steps<LIMIT:
    s=tape[pos]; t=T[(st,s)]
    if t is None: print("HALT",steps);break
    w,d,ns=t
    if st=='A' and d==-1:
        events.append((steps,pos))
        snaps[steps]=(pos, tape[max(lo-2,0):hi+2], lo-2, tape[pos+1])
    tape[pos]=w; pos+=d; st=ns; steps+=1
    lo=min(lo,pos); hi=max(hi,pos)
    if w==1 and (m is None or pos-d<m): m=pos-d; fronts.append((steps,m))
groups=[]; g=None
for (t_,p) in events:
    if g is None or t_-g[-1][0]>6:
        if g: groups.append(g)
        g=[(t_,p)]
    else: g.append((t_,p))
if g: groups.append(g)
fs=[f[0] for f in fronts]
for g in groups:
    span=g[0][1]-g[-1][1]
    if span<5: continue
    t0,p0=g[0]
    p,tp,off,rn = snaps[t0]
    mm=fronts[bisect.bisect_right(fs,t0)-1][1]
    # simulate automaton from p0 leftwards; mode determined by right neighbour
    mode = 'P' if rn==2 else ('Q' if rn==3 else '?')
    i=p0; path=[]
    while True:
        c=tp[i-off]
        path.append(str(c))
        if c==1: res=('HALT',i-mm); break
        if mode=='P':
            if c==3: mode='P'
            elif c==0: mode='Q'
            else: res=('stop',i-mm,c,'P'); break
        else:
            if c==3: mode='P'
            elif c==2: mode='P'
            else: res=('stop',i-mm,c,'Q'); break
        i-=1
    print(f"t={t0} start={p0-mm} mode0={ 'P' if rn==2 else rn} predicted={res} actual_end={g[-1][1]-mm} path={''.join(path)}")
