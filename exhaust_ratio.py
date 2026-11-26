import math
from sample_ratio import ht
best=(0,None)
viol=[]
for a in range(1,2000):
    for c in range(1,2000):
        T=ht(a,c,5000)
        # candidate T <= 2*log2(a+2)+2
        if T > 2*math.log2(a+2)+2:
            viol.append((T,a,c,T/math.log2(a+2)))
        if T/math.log2(a+2) > best[0]: best=(T/math.log2(a+2),(T,a,c))
print('best',best,'viol',len(viol))
print(sorted(viol,reverse=True)[:10])
