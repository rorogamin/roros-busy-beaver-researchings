import sys
sys.path.insert(0,'tools')
import eps1_machine as em, eps1_copy as cp
OFF=em.OFF; S=lambda i: OFF+i
def ones(n): return [1]*n
def zeros(n): return [0]*n
D,kk,c,Y,far = 2,1,1,[1,1,0],4
A=zeros(far)
clft=[0]+[0,1,0,0]+zeros(D)+ones(kk+1)+A   # trip_frame 0 D (kk) A, kk = S n -> ones (S kk)
print('start clft far->near:',list(reversed(clft)))
t={0:1}
for i,x in enumerate(clft): t[-1-i]=x
for i,x in enumerate([c]+Y): t[1+i]=x
h=0; st=S(cp.R3); mm=em.machine(); last=None
for step in range(1,60):
    r=mm.step(t,h,st)
    if r is None: print('HALT'); break
    h,st=r
    if st!=last:
        L=[t.get(h-1-i,0) for i in range(12)]
        R=[t.get(h+1+i,0) for i in range(12)]
        print('%3d %-3s cur=%d Lnear->far=%s Rnear->far=%s'%(step,em.NAMES.get(st,st),t.get(h,0),L,R))
        last=st
    if st==S(cp.R3) and step>5: break
