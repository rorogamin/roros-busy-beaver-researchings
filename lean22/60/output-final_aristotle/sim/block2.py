from sim import M, T
def run_block(st, side, blk):
    b=list(blk); k=len(b)
    p = 0 if side=='L' else k-1
    s = st
    n=0
    while True:
        r=T[(s,b[p])]
        if r is None: return (tuple(b),'H',None,n)
        w,d,ns=r
        b[p]=w; p+=d; s=ns; n+=1
        if p<0: return (tuple(b),'L',s,n)
        if p>=k: return (tuple(b),'R',s,n)
        if n>10000: return (tuple(b),'INF',None,n)

def analyze(k, offset, N=300000):
    m=M(); entries={}
    while m.t<N:
        p0=m.pos
        if not m.step(): break
        bi0=(p0-offset)//k; bi1=(m.pos-offset)//k
        if bi1!=bi0:
            side='L' if m.pos>p0 else 'R'
            blk=tuple(m.tape.get(offset+bi1*k+j,0) for j in range(k))
            key=(m.st,side,blk)
            entries[key]=entries.get(key,0)+1
    return entries
import collections
for k,off in ((3,0),(3,1),(3,2)):
    e=analyze(k,off)
    print('=== k=%d off=%d, %d entries'%(k,off,len(e)))
    for (s,sd,b),c in sorted(e.items(), key=lambda x:-x[1]):
        nb,ex,ns,n=run_block(s,sd,b)
        print('  %s%s %s -> %s %s%s  (%d steps) x%d'%(s,'>' if sd=='L' else '<',''.join(map(str,b)),''.join(map(str,nb)),ns,ex,n,c))
