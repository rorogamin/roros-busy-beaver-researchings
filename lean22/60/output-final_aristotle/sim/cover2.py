from sim import M
from collections import Counter

def g(m,i): return m.tape.get(i,0)

def runlen_left(m,p,v):
    k=0
    while g(m,p-k)==v: k+=1
    return k
def runlen_right(m,p,v):
    k=0
    while g(m,p+k)==v: k+=1
    return k

def rules(m):
    p=m.pos; s=m.st
    if s=='A':
        if g(m,p)==0 and g(m,p-1)==0 and g(m,p+1)==0: return ('leftExtend',5)
        if g(m,p)==0:
            j=0
            while g(m,p+1+j)==4: j+=1
            if g(m,p+1+j)==2: return ('blockR(j)', j+2)
        if g(m,p)==3:
            if g(m,p-1)==1: return ('blockL_13',2)
            if g(m,p-1)==0 and g(m,p-2)==1: return ('blockL_103',3)
            if g(m,p-1)==0 and g(m,p-2)==0 and g(m,p-3)==1: return ('blockL_1003',6)
            if g(m,p-1)==0 and g(m,p-2)==0 and g(m,p-3)==0: return ('turnWall',9)
            k=runlen_left(m,p,3)
            if k>1: return ('run_threes(A)',k)
        if g(m,p)==1 and g(m,p-1)==3 and g(m,p-2)==0: return ('sweepL_031',3)
        if g(m,p)==1:
            k=runlen_left(m,p,1)
            return ('run_ones_A',k)
        if g(m,p)==2 and g(m,p-1)==3 and g(m,p-2)==0 and g(m,p+1)==2: return ('wall_step',8)
    else:
        if g(m,p)==2 and g(m,p+1)==0 and g(m,p+2)==4: return ('sweepR_204',3)
        if g(m,p)==4 and g(m,p+1)==2 and g(m,p+2)==0: return ('sweepR_420',3)
        if g(m,p)==0 and g(m,p-1)==1 and g(m,p-2)==3: return ('sweepL_310',3)
        if g(m,p)==1:
            k=runlen_left(m,p,1)
            return ('run_ones_B',k)
        if g(m,p)==4:
            k=runlen_right(m,p,4)
            return ('run_fours_B',k)
        if g(m,p)==3:
            k=runlen_left(m,p,3)
            if k>1: return ('run_threes(B)',k)
    return None

def run(N):
    m=M()
    used=Counter(); miss=Counter(); covered=0
    while m.t<N:
        r=rules(m)
        if r:
            name,n=r
            used[name]+=1
            for _ in range(n):
                if not m.step(): print('HALT!'); return
            covered+=n
        else:
            w=''.join(str(g(m,m.pos+d)) for d in range(-4,5))
            miss[(m.st,w)]+=1
            m.step()
    print('steps',m.t,'covered',covered, '%.4f'%(covered/m.t))
    print('rules used:', used.most_common(30))
    print('missing contexts:', len(miss), 'total missed steps', sum(miss.values()))
    for k,v in miss.most_common(25): print('   ',k,v)
run(200000)
