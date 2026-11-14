import sys, itertools
T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}
def saturate(k, w):
    # head view: (state, tuple of 2k+1 symbols), head at index k
    P=set()
    def subwords(tup):
        return {tup[i:i+w] for i in range(len(tup)-w+1)} if len(tup)>=w else set()
    start=('A',tuple([0]*(2*k+1)))
    P |= subwords(start[1])
    H={start}
    frontier=[start]
    halt=None
    while frontier:
        s,W=frontier.pop()
        r=T[(s,W[k])]
        if r is None:
            return ('HALT',(s,W),len(H),len(P))
        wr,d,s2=r
        W2=list(W); W2[k]=wr
        new=subwords(tuple(W2))
        newP=[x for x in new if x not in P]
        if newP:
            P|=set(newP)
            # re-add all H to frontier since P grew
            frontier=list(H)
        if d==+1:
            base=tuple(W2[1:])
            for e in range(5):
                cand=base+(e,)
                if all(x in P for x in subwords(cand)):
                    h=(s2,cand)
                    if h not in H:
                        H.add(h); frontier.append(h)
        else:
            base=tuple(W2[:-1])
            for e in range(5):
                cand=(e,)+base
                if all(x in P for x in subwords(cand)):
                    h=(s2,cand)
                    if h not in H:
                        H.add(h); frontier.append(h)
    return ('OK',None,len(H),len(P))
for w in range(2,8):
  for k in range(1,6):
    if 2*k+1 < w: continue
    r=saturate(k,w)
    print('k=%d w=%d ->'%(k,w), r[0], r[2], r[3], r[1] if r[0]=='HALT' else '')
    sys.stdout.flush()
