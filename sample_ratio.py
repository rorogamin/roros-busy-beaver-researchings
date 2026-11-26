import random, math

def step(a,c):
    if c+1<=a and c%2==0: return a-c-1, 3*(c//2)+2, False
    if c+2<=a and c%4==1: return a-c-2, 3*(c//2)+5, False
    if c+4<=a and c%4==3: return a-c-4, 3*(c//2)+8, False
    if c+3==a and c%4==3: return a,c,True
    if c+2==a and c%4==3: return 3*c+8,1,False
    if c+1==a and c%2==1: return a,c,True
    if c>=a and a%2==0 and c%2==0: return a,c,True
    if c>=a and a%2==0 and c%2==1: return 1,a//2+c+2,False
    if c>=a and a%2==1 and c%2==0: return 3*a,c-a+4,False
    if c>=a and a%2==1 and c%2==1: return 3*a+2,c-a+1,False
    raise Exception('no rule',a,c)

def ht(a,c,cap=20000):
    c0=c
    for n in range(1,cap+1):
        a2,c2,h=step(a,c)
        if h or a2==1 or 2*c2<=c0: return n
        a,c=a2,c2
    return cap

random.seed(1)
worst=[]
for bits in [8,16,32,64,128,256,465,600,1000]:
    best=0
    for _ in range(300):
        a=random.getrandbits(bits)|1
        c=random.getrandbits(bits)|1
        T=ht(a,c)
        r=T/math.log2(max(a,c,2))
        if r>best: best=r; b=(T,a.bit_length(),c.bit_length())
    print(bits,best,b)
