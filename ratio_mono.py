import math
def step(a,c):
    if c+1<=a and c%2==0: return a-c-1, 3*(c//2)+2, False,'a'
    if c+2<=a and c%4==1: return a-c-2, 3*(c//2)+5, False,'b'
    if c+4<=a and c%4==3: return a-c-4, 3*(c//2)+8, False,'c'
    if c+3==a and c%4==3: return a,c,True,'d'
    if c+2==a and c%4==3: return 3*c+8,1,False,'e'
    if c+1==a and c%2==1: return a,c,True,'f'
    if c>=a and a%2==0 and c%2==0: return a,c,True,'g'
    if c>=a and a%2==0 and c%2==1: return 1,a//2+c+2,False,'h'
    if c>=a and a%2==1 and c%2==0: return 3*a,c-a+4,False,'i'
    if c>=a and a%2==1 and c%2==1: return 3*a+2,c-a+1,False,'j'
def trace(a,c,cap=20000):
    c0=c; rs=[]; states=[]
    for n in range(1,cap+1):
        a2,c2,h,r=step(a,c); rs.append(r); states.append((a,c))
        if h or a2==1 or 2*c2<=c0: return n,rs,states
        a,c=a2,c2
    return cap,rs,states
import random
random.seed(2)
bad=0; worst=(0,None)
for bits in [8,16,32,64,128,256,465]:
  for _ in range(200):
    a=random.getrandbits(bits)|1; c=random.getrandbits(bits)|1
    n,rs,st=trace(a,c)
    r=[abs(math.log(max(x,1)/max(y,1))) for x,y in st]
    # count increases >0.01
    inc=sum(1 for i in range(1,len(r)) if r[i]>r[i-1]+0.01)
    if inc: bad+=1
    if inc>worst[0]: worst=(inc,(bits,n,rs))
print('bad traces',bad,'worst inc',worst[0],worst[1][:2] if worst[1] else None)
if worst[1]:
  bits,n,rs=worst[1]
  # print run letters around increases? just runs
  runs=[]
  for x in rs:
    if runs and runs[-1][0]==x: runs[-1][1]+=1
    else: runs.append([x,1])
  print(runs[:50])
