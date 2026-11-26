from ratio_mono import step
import random, math
from z3 import *
def feat(a,c):
 a=max(a,1); c=max(c,1); S=a+c
 return [math.log2(a),math.log2(c),math.log2(S),math.log2(abs(a-c)+1),math.log2(min(a,c)),math.log2(max(a,c)),abs(math.log2(a/c)),1.0]
trans=[]
def add(a,c):
 c0=c
 for n in range(1,5000):
  a2,c2,h,r=step(a,c)
  if h or a2==1 or 2*c2<=c0: return
  trans.append((feat(a,c),feat(a2,c2))); a,c=a2,c2
random.seed(0)
for _ in range(80):
 a=random.getrandbits(random.randint(2,200))|1; c=random.getrandbits(random.randint(2,200))|1; add(a,c)
for k in range(1,60):
 a=2*3**k-1
 for c in [1,2,3,4,5,7,10,100,2047]: add(a,c)
print('trans',len(trans))
n=8; w=[Real('w%d'%i) for i in range(n)]; o=Solver()
for f,g in trans:
 o.add(Sum([w[i]*(g[i]-f[i]) for i in range(n)]) <= -1)
# require bounded F0 on postj: test objective later; just feasibility
o.add(Sum([w[i] for i in range(n-1)])>=0)
print(o.check())
if o.check()==sat:
 m=o.model(); vals=[m.eval(x) for x in w]; print(vals)
 # check max F0 postj k<=292
 mx=0
 for k in range(1,293):
  a=2*3**k-1
  for c in [1,3,2047]:
   f=feat(a,c); F=sum(float(vals[i].as_fraction())*f[i] for i in range(n)); mx=max(mx,F)
 print('maxF postj',mx)
