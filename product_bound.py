from ratio_mono import step
def ht(a,c,cap=20000):
    c0=c
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c)
        if h or a2==1 or 2*c2<=c0: return n
        a,c=a2,c2
    return cap
best=(0,None)
for a in range(2,1500):
  for c in range(1,1500):
    T=ht(a,c,5000); P=a*c
    r=(2**T)/(P**2)
    if r>best[0]: best=(r,(T,a,c,P))
print('max 2^T/(ac)^2',best)
# postj
best=(0,None)
for k in range(1,200):
    a=2*3**k-1
    for c in range(1,300):
        if c>=a: break
        T=ht(a,c,5000); P=a*c
        r=(2**T)/(P**2)
        if r>best[0]: best=(r,(T,k,c,P))
print('postj max',best)
