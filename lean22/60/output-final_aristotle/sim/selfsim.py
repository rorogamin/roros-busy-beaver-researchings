from sim import T
def U(a,b): return [0]+[4]*a+[2]*b
def run_trace(win,nleft=3):
    tape={}
    for i,v in enumerate(win): tape[i]=v
    pos=0; st='B'; out=[]
    for t in range(100000):
        out.append((st,pos,''.join(str(tape.get(i,0)) for i in range(-3,len(win)))))
        r=T[(st,tape.get(pos,0))]
        if r is None: break
        w,d,ns=r; tape[pos]=w; pos+=d; st=ns
        if pos==-3 and ns=='B':
            out.append((st,pos,''.join(str(tape.get(i,0)) for i in range(-3,len(win)))))
            break
    return out
for m in (2,3):
    tr=run_trace(U(2,1)+U(4,1)+U(1,2*m)+[0])
    print('m=%d steps=%d'%(m,len(tr)-1))
A=run_trace(U(2,1)+U(4,1)+U(1,4)+[0])
B=run_trace(U(2,1)+U(4,1)+U(1,6)+[0])
# find t such that B[t] config equals A[t-20] with 2 extra cells inserted somewhere
for t in range(len(B)):
    for s in range(max(0,t-40),min(len(A),t+1)):
        stB,pB,wB=B[t]; stA,pA,wA=A[s]
        if stB==stA and pB==pA and len(wB)==len(wA)+2:
            # check wB = wA with 2 chars inserted at some position after pos
            for i in range(len(wA)+1):
                if wB[:i]+wB[i+2:]==wA:
                    print('B[%d] ~ A[%d] insert at %d (abs %d) pos=%d st=%s'%(t,s,i,i-3,pB,stB))
                    break
            else: continue
            break

print('=== check B[t+20] ~ A[t]')
first=None
for t in range(len(A)):
    if t+20>=len(B): break
    stB,pB,wB=B[t+20]; stA,pA,wA=A[t]
    ok=None
    if stB==stA and pB==pA:
        for i in range(len(wA)+1):
            if wB[:i]+wB[i+2:]==wA: ok=i; break
    if ok is not None:
        if first is None: first=t; print('first match t=%d ins=%d'%(t,ok-3))
    else:
        if first is not None: print('break at t=%d'%t); first=None
print('end t=%d (len A=%d)'%(len(A)-1,len(A)))
