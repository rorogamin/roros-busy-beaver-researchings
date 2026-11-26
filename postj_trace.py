from ratio_mono import step
import random
def trace(a,c,cap=20000):
    c0=c; rs=[]; states=[]
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c); rs.append(r); states.append((a,c))
        if h or a2==1 or 2*c2<=c0: return n,rs,states,(a2,c2,h)
        a,c=a2,c2
    return cap,rs,states,(a,c,False)
random.seed(5)
best=(0,None)
for k in list(range(1,30))+[50,100,200,289,292]:
    a=2*(3**k)-1
    for _ in range(50):
        c=random.randrange(1,2*(3**k))
        n,rs,st,end=trace(a,c)
        runs=[]
        for x in rs:
            if runs and runs[-1][0]==x: runs[-1][1]+=1
            else: runs.append([x,1])
        if n>best[0]: best=(n,(k,c,runs[:20],len(runs),end[0].bit_length(),end[1]))
print('best',best[0],'k',best[1][0],'nruns',best[1][3])
print(best[1][2])
# extrema c=1, max
for k in [10,50,289,292]:
    a=2*3**k-1
    for c in [1,2,3,2*3**k-1]:
        n,rs,st,end=trace(a,c)
        runs=[]
        for x in rs:
            if runs and runs[-1][0]==x: runs[-1][1]+=1
            else: runs.append([x,1])
        print('k',k,'c',c,'T',n,'runs',len(runs),runs[:12])
