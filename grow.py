from ratio_mono import step
import random,math
def stats(a,c,cap=20000):
    c0=c; S0=a+c; mx=S0; r0=abs(math.log(max(a,1)/max(c,1))); mr=r0
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c)
        S=a+c; mx=max(mx,S)
        rr=abs(math.log(max(a,1)/max(c,1))); mr=max(mr,rr)
        if h or a2==1 or 2*c2<=c0: return n,mx/S0,mr/(r0+1)
        a,c=a2,c2
    return cap,mx/S0,mr/(r0+1)
bestS=(0,None); bestR=(0,None)
for a in range(2,300):
  for c in range(1,300):
    t,gs,gr=stats(a,c,5000)
    if gs>bestS[0]: bestS=(gs,(t,a,c))
    if gr>bestR[0]: bestR=(gr,(t,a,c))
print('best growth S',bestS,'best ratio growth',bestR)
random.seed(3)
for bits in [32,64,128,256,465]:
  bs=br=0; arg=None
  for _ in range(200):
    a=random.getrandbits(bits)|1; c=random.getrandbits(bits)|1
    t,gs,gr=stats(a,c)
    if gs>bs: bs=gs; arg=(t,a.bit_length(),c.bit_length())
    br=max(br,gr)
  print(bits,'Sgrowth',bs,arg,'ratio',br)
