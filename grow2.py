from ratio_mono import step
def maxgrowth(a,c,cap=20000):
    c0=c; S0=a+c; mx=S0
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c)
        mx=max(mx,a+c)
        if h or a2==1 or 2*c2<=c0: return mx/S0,n
        a,c=a2,c2
    return mx/S0,cap
best=(0,None)
for c in range(1,101):
  for a in range(c,5000):
    g,n=maxgrowth(a,c)
    if g>best[0]: best=(g,(a,c,n))
print('best c<=100,a<5000',best)
best=(0,None)
for a in range(2,101):
  for c in range(1,5000):
    g,n=maxgrowth(a,c)
    if g>best[0]: best=(g,(a,c,n))
print('best a<=100,c<5000',best)
