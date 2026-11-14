import sys
from sim import T

def run_block(st, side, blk):
    """side='L' entering from left (moving right), 'R' entering from right (moving left).
    Returns (newblk, exitside, newstate) or ('HALT',...)"""
    b=list(blk); k=len(b)
    p = 0 if side=='L' else k-1
    s = st
    for _ in range(10000):
        r=T[(s,b[p])]
        if r is None: return (tuple(b),'H',None)
        w,d,ns=r
        b[p]=w; p+=d; s=ns
        if p<0: return (tuple(b),'L',s)
        if p>=k: return (tuple(b),'R',s)
    return (tuple(b),'INF',None)

def analyze(k, offset, N=2000000):
    from sim import M
    m=M()
    # occurrences: dict (state, side, blk) -> (newblk, exitside, newstate)
    occ={}
    # simulate at block level
    # tape as dict blockindex -> tuple
    def getblk(bi):
        return tuple(m.tape.get(offset+bi*k+j,0) for j in range(k))
    # find current block
    while m.t<N:
        bi = (m.pos-offset)//k
        r = (m.pos-offset)%k
        # only record when head is at a block boundary
        if r==0 or r==k-1:
            side = 'L' if r==0 else 'R'
            # determine direction: we record entering
            pass
        m.step()
    return occ

# simpler: simulate normally, and whenever head crosses a block boundary record the entry
def analyze2(k, offset, N=1000000):
    from sim import M
    m=M()
    seen={}
    entries=set()
    cur=None
    while m.t<N:
        bi=(m.pos-offset)//k; r=(m.pos-offset)%k
        if (r==0 and cur!=('L',bi)) or (r==k-1 and cur!=('R',bi)):
            pass
        p0=m.pos
        if not m.step(): break
        bi0=(p0-offset)//k; bi1=(m.pos-offset)//k
        if bi1!=bi0:
            side='L' if m.pos>p0 else 'R'
            blk=tuple(m.tape.get(offset+bi1*k+j,0) for j in range(k))
            entries.add((m.st,side,blk))
    return entries

for k in (2,3,4,6):
  for off in range(k):
    e=analyze2(k,off,300000)
    # which (state,side) combos
    combos=sorted(set((s,sd) for s,sd,b in e))
    print('k=%d off=%d entries=%d combos=%s'%(k,off,len(e),combos))
