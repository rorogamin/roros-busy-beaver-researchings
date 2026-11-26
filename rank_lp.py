from ratio_mono import step
from z3 import *
import random
bl=lambda x:max(0,x.bit_length())
def feat(a,c):
 return [bl(a),bl(c),bl(a+c),bl(abs(a-c)),bl(min(a,c)),bl(max(a,c)),1]
trans=[]
def add(a,c,cap=20000):
 c0=c
 for n in range(1,cap+1):
  a2,c2,h,r=step(a,c)
  if h or a2==1 or 2*c2<=c0: return
  trans.append((feat(a,c),feat(a2,c2)))
  a,c=a2,c2
# exhaustive small
for a in range(2,300):
 for c in range(1,300): add(a,c)
random.seed(1)
for bits in [32,64,128,256,465]:
 for _ in range(100):
  a=random.getrandbits(bits)|1; c=random.getrandbits(bits)|1; add(a,c)
for k in range(1,100):
 a=2*3**k-1
 for c in list(range(1,100))+[random.randrange(1,a) for _ in range(20)]: add(a,c)
print('trans',len(trans))
w=[Real('w%d'%i) for i in range(7)]
o=Optimize()
# F next <= F - 1
for f,g in trans:
 o.add(Sum([w[i]*g[i] for i in range(7)]) <= Sum([w[i]*f[i] for i in range(7)]) - 1)
# positivity/normalization
for i in range(6): o.add(w[i]>=0)
o.add(w[6]>=0)
# minimize max F at postj sample
F0s=[]
for k in range(1,100):
 a=2*3**k-1
 for c in range(1,100):
  f=feat(a,c); F0s.append(Sum([w[i]*f[i] for i in range(7)]))
obj=Real('obj')
for F in F0s: o.add(obj>=F)
o.minimize(obj)
print(o.check())
m=o.model()
print([m.eval(wi) for wi in w], 'obj',m.eval(obj))
