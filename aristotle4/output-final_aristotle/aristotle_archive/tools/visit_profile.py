import sys
T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
 ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
N=4000; tape=[0]*N; pos=N//2; st='A'; lo=hi=pos; steps=0
LIMIT=int(sys.argv[1]); E0=int(sys.argv[2])
m=None; t0=0; visits=None; epoch=0
while steps<LIMIT:
    if visits is not None: visits[pos]=visits.get(pos,0)+1
    t=T[(st,tape[pos])]
    if t is None: print("HALT",steps);break
    w,d,ns=t; tape[pos]=w; pos+=d; st=ns; steps+=1
    lo=min(lo,pos); hi=max(hi,pos)
    if w==1 and (m is None or pos-d<m):
        if visits is not None:
            print("epoch",epoch,"t0",t0,"len",steps-t0,"m",m-lo)
            print("  visit profile (cell rel m : count):")
            print("   ", ' '.join(f"{i-m}:{visits.get(i,0)}" for i in range(m,hi+1)))
            print("  tape at end:", ''.join(str(tape[i]) for i in range(m,hi+1)))
            break
        epoch+=1
        m=pos-d; t0=steps
        if epoch==E0: visits={}
