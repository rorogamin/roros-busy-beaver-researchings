# cell transducer on {A,B}; state (s,f)
def step(st,x):
    s,f=st
    if s==0: return ((3,True),'B') if x=='A' else ((2,False),'')
    if s==1: return ((2,True),'A') if x=='A' else ((3,f),'')
    if s==2:
        if x=='A': return ((1,f),'')
        return ((2,True),'BA') if f else ((3,True),'B')
    if s==3:
        if x=='A':
            if f: return ((2,True),'B')
            return None
        return ((1,True),'A')
def run(w):
    st=(0,False);out=[]
    for i,x in enumerate(w):
        r=step(st,x)
        if r is None: return None,i
        st,o=r;out.append(o)
    return ''.join(out),st
if __name__=="__main__":
    w="A"+"BABAB"*4000
    for c in range(20):
        print(c,len(w),w[:60])
        o,st=run(w)
        if o is None: print('HALT at',st);break
        w=o
