from sim import T
def runwin(win, nleft=3, tailsym=None):
    """win: list of cell values starting at pos 0; cells -nleft..-1 = 0.
    tail cells >= len(win) are 'poison' (we detect if read)."""
    tape={}
    for i,v in enumerate(win): tape[i]=v
    for i in range(1,nleft+1): tape[-i]=0
    pos=0; st='B'; t=0; lo=0; hi=0
    while True:
        if pos>=len(win) or pos< -nleft: return ('OUT',t,pos)
        r=T[(st,tape[pos])]
        if r is None: return ('HALT',t)
        w,d,ns=r; tape[pos]=w; pos+=d; st=ns; t+=1
        lo=min(lo,pos);hi=max(hi,pos)
        if pos==-3 and st=='B':
            return ('OK',t,lo,hi,[tape.get(i,0) for i in range(-3,len(win))])
        if t>100000: return ('TO',)
def U(a,b): return [0]+[4]*a+[2]*b
def V(c): return [4,3]+[2]*c
print('R2:', runwin(U(2,2)+U(1,1)[:1]))   # 0 4 4 2 2 then 0
print('R2 wide:', runwin(U(2,2)+[0]))
for b in (2,3,4,5,6,8):
    print('R1 b=%d:'%b, runwin(U(2,1)+U(4,1)+U(1,b)+[0]))
for b in (2,3,4,5,6,8):
    print('R3 b=%d:'%b, runwin(U(2,2)+V(1)+U(1,1)+U(1,b)+[0]))
print('--- P3 with U(2,b)')
for b in (2,4,6,8,10):
    print('b=%d:'%b, runwin(U(2,2)+V(1)+U(1,1)+U(2,b)+[0]))
print('--- P1 with U(2,b)')
for b in (2,4,6,8):
    print('b=%d:'%b, runwin(U(2,1)+U(4,1)+U(2,b)+[0]))
print('--- P3 with u^k U(1,b)')
for k in (1,2,3):
    print('k=%d:'%k, runwin(U(2,2)+V(1)+U(1,1)+U(1,1)*k+U(1,4)+[0]))
