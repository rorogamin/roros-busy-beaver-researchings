exec(open('fit.py').read().split('tests=')[0])
import random
random.seed(3)
def genR(maxm=7):
    R=[]
    while len(R)<random.randint(1,maxm):
        r=random.random()
        if r<0.4: R.append(('U',random.choice([1,2,4,10,28]),1))
        elif r<0.7: R.append(('U',random.choice([1,2]),random.randint(1,14)))
        else:
            R.append(('U',random.choice([1,2]),random.randint(2,14)))
            R.append(('V',random.randint(0,14))); R.append(('U',1,1))
    return R
bad=0; ts=set()
for _ in range(400):
    R=genR()
    W=[('U',2,2),('U',1,1)]+R
    r=run(W,20000000)
    exp=[('U',2,2),('V',1),('U',1,1)]+R
    if r[0]!='OK' or r[1]!=exp: bad+=1; print('BAD',fmt(R),r[0],fmt(r[1]) if r[0]=='OK' else '')
    else: ts.add(r[2])
print('bad',bad,'steps set',sorted(ts)[:10])
