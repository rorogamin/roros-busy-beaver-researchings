from ratio_mono import step
def walk(a,c,cap=20000):
    c0=c; out=[]
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c)
        out.append((r,(a+c),a,c,(a2+c2),a2,c2,h,a2==1 or 2*c2<=c0))
        if h or a2==1 or 2*c2<=c0: return n,out
        a,c=a2,c2
    return cap,out
best=(9,None)
for a in range(2,500):
 for c in range(1,500):
  n,out=walk(a,c,5000)
  for rec in out:
   r,S,a0,c0,S2,a2,c2,h,stop=rec
   q=S2/S if S else 9
   if q<best[0]: best=(q,(r,S,a0,c0,S2,a2,c2,n,h,stop))
print('min S ratio',best)
