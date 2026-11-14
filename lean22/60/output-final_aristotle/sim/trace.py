from sim import T
def show(tape,pos,st,lo,hi):
    s=''
    for i in range(lo,hi+1):
        if i==pos: s+='['+st+']'
        s+=str(tape.get(i,0))
    return s
def tr(win,nleft=3,N=200):
    tape={}
    for i,v in enumerate(win): tape[i]=v
    pos=0; st='B'
    lo=-nleft; hi=len(win)-1
    for t in range(N):
        print('%4d %s'%(t, show(tape,pos,st,lo,hi)))
        r=T[(st,tape.get(pos,0))]
        if r is None: print('HALT'); return
        w,d,ns=r; tape[pos]=w; pos+=d; st=ns
        if pos==-3 and ns=='B': print('%4d %s  END'%(t+1,show(tape,pos,st,lo,hi))); return
def U(a,b): return [0]+[4]*a+[2]*b
tr(U(2,1)+U(4,1)+U(1,6)+[0])
