import sys
T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
 ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
N=4000; tape=[0]*N; pos=N//2; st='A'; lo=hi=pos; steps=0
LIMIT=int(sys.argv[1]); E0=int(sys.argv[2]); J=int(sys.argv[3])
m=None; epoch=0; L=None; lastcross=None; out=[]
while steps<LIMIT:
    t=T[(st,tape[pos])]
    if t is None: print("HALT",steps);break
    w,d,ns=t; prev=pos
    tape[pos]=w; pos+=d; st=ns; steps+=1
    lo=min(lo,pos); hi=max(hi,pos)
    if L is not None:
        if prev==L and pos==L+1:   # exiting left region
            out.append(('out',st,steps-lastcross if lastcross else 0))
            lastcross=steps
        elif prev==L+1 and pos==L: # entering left region
            out.append(('in',st,steps-lastcross if lastcross else 0))
            lastcross=steps
    if w==1 and (m is None or pos-d<m):
        if L is not None:
            print("epoch",epoch,"crossings",len(out))
            print(" durations (in->out):", [o[2] for o in out[:80]])
            print(" states:", ''.join(o[1] for o in out[:80]))
            break
        epoch+=1; m=pos-d
        if epoch==E0:
            L=m+J; lastcross=steps
