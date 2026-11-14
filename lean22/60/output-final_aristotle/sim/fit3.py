exec(open('fit.py').read().split('tests=')[0])
import random
def genR(maxm=6):
    R=[]
    while len(R)<random.randint(1,maxm):
        r=random.random()
        if r<0.4: R.append(('U',random.choice([1,2,4,10]),1))
        elif r<0.7: R.append(('U',random.choice([1,2]),2*random.randint(1,6)))
        else:
            R.append(('U',random.choice([1,2]),2*random.randint(1,6)))
            R.append(('V',2*random.randint(0,6)+1)); R.append(('U',1,1))
    if not (R[-1][0]=='U' and R[-1][2]==1): R.append(('U',1,1))
    return R
prefs={'P1':[('U',2,1),('U',4,1)],'P2':[('U',2,2),('U',1,1)],'P3':[('U',2,2),('V',1),('U',1,1)]}
random.seed(11)
import collections
stats=collections.Counter(); ex=collections.defaultdict(list)
for _ in range(300):
    R=genR()
    for k,p in prefs.items():
        r=stepW(p+R,20000000)
        stats[(k,r[0])]+=1
        if r[0]!='OK' and len(ex[k])<4: ex[k].append((fmt(R),r[:2]))
print(stats)
for k in ex:
    for e in ex[k][:4]: print(k,e)
