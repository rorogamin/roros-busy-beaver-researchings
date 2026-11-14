import sys
T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
 ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
N=4000; tape=[0]*N; pos=N//2; st='A'; lo=hi=pos; steps=0
LIMIT=int(sys.argv[1]); E0=int(sys.argv[2]); J=int(sys.argv[3]); CNT=int(sys.argv[4])
DIG={3:0,4:1,0:2}
m=None; epoch=0; L=None; n=0
def tern(m,L):
    # cells m+1..L, MSB at m+1
    v=0
    for i in range(m+1,L+1):
        d=DIG.get(tape[i],None)
        if d is None: return None
        v=v*3+d
    return v
def binr(L):
    v=0; i=L+1; bits=[]
    while i+1<=hi:
        p=(tape[i],tape[i+1])
        if p==(2,4): bits.append(0)
        elif p==(4,4): bits.append(1)
        else: break
        i+=2
    return ''.join(map(str,bits)), i-(L+1)
while steps<LIMIT:
    t=T[(st,tape[pos])]
    if t is None: print("HALT",steps);break
    w,d,ns=t; prev=pos
    tape[pos]=w; pos+=d; st=ns; steps+=1
    lo=min(lo,pos); hi=max(hi,pos)
    if L is not None and ((prev==L and pos==L+1) or (prev==L+1 and pos==L)):
        dirn = 'R' if pos>prev else 'L'
        b,blen=binr(L)
        print(f"t={steps} {dirn} st={st} tern={tern(m,L)} bin(lsb-first)={b} blen={blen}")
        n+=1
        if n>=CNT: sys.exit()
    if w==1 and (m is None or pos-d<m):
        epoch+=1; m=pos-d
        if epoch==E0: L=m+J
