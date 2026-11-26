from ratio_mono import step
def minFratio(a,c):
    c0=c; worst=99; rec=None
    for n in range(1,20000):
        a2,c2,h,r=step(a,c)
        F=((min(a,c)+1)**2)*((a+c+1)**4)
        F2=((min(a2,c2)+1)**2)*((a2+c2+1)**4)
        if F>0 and F2/F<worst: worst=F2/F; rec=(n,r,a,c,a2,c2,F2/F)
        if h or a2==1 or 2*c2<=c0: return worst,rec
        a,c=a2,c2
    return worst,rec
best=(99,None)
for a in range(2,400):
 for c in range(1,400):
   w,rec=minFratio(a,c)
   if w<best[0]: best=(w,(a,c,rec))
print('worst minF ratio',best)
