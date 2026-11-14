from sim import T
# start: state B at 0, cells 0..7 = 0 4 4 2 2 0 4 2, cells >=8 arbitrary X (use symbolic: just check head range)
def go(tail):
    tape={}
    w=[0,4,4,2,2,0,4,2]+tail
    for i,v in enumerate(w): tape[i]=v
    pos=0; st='B'; lo=0; hi=0
    for t in range(31):
        r=T[(st,tape.get(pos,0))]
        assert r, (t,pos,st)
        wr,d,ns=r; tape[pos]=wr; pos+=d; st=ns
        lo=min(lo,pos); hi=max(hi,pos)
    return pos,st,lo,hi,[tape.get(i,0) for i in range(-3,8)]
for tail in ([0]*6,[0,4,2]*2,[4,3,2,0,4,2],[0,4,4,4,2,2],[0]*3+[4,4,2]):
    print(tail, go(tail))
