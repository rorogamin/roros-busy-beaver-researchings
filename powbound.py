from ratio_mono import step
def ht(a,c,cap=20000):
    c0=c
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c)
        if h or a2==1 or 2*c2<=c0: return n
        a,c=a2,c2
    return cap
best=(0,None)
for a in range(2,2000):
  for c in range(1,2000):
    T=ht(a,c,5000); S=a+c
    r=(2**T)/(S**6)
    if r>best[0]: best=(r,(T,a,c,S))
print('max 2^T/S^6',best)
# test 2^T <= 64 S^6
cnt=0
for a in range(2,1000):
  for c in range(1,1000):
    T=ht(a,c,5000); S=a+c
    if 2**T > 64*S**6: cnt+=1
print('viol 64S6',cnt)
