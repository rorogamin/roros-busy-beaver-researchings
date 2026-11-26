from ratio_mono import step
import random
from z3 import *
bl=lambda x:x.bit_length()
def feat(a,c): return [bl(a),bl(c),bl(a+c),bl(abs(a-c)),bl(min(a,c)),bl(max(a,c)),1]
trans=[]
def add(a,c):
 c0=c
 for n in range(1,5000):
  a2,c2,h,r=step(a,c)
  if h or a2==1 or 2*c2<=c0: return
  trans.append((feat(a,c),feat(a2,c2)))
  a,c=a2,c2
random.seed(0)
for _ in range(300):
 a=random.getrandbits(random.randint(2,465))|1; c=random.getrandbits(random.randint(2,465))|1; add(a,c)
for k in range(1,80):
 a=2*3**k-1
 for c in [1,2,3,4,5,7,10,100,2047,random.randrange(1,a)]: add(a,c)
print('trans',len(trans),flush=True)
w=[Real('w%d'%i) for i in range(7)]
o=Solver()
for f,g in trans: o.add(Sum([w[i]*g[i] for i in range(7)]) <= Sum([w[i]*f[i] for i in range(7)]) - 1)
for i in range(6): o.add(w[i]>=0)
o.add(w[6]>=0, Sum(w)>=1)
print(o.check(),flush=True)
if o.check()==sat:
 m=o.model(); print([m.eval(x) for x in w])
