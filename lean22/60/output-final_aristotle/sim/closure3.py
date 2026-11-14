import random
exec(open('closure.py').read().split('random.seed')[0])
def gen(maxm=8):
    toks=[]
    m=random.randint(1,maxm)
    i=0
    while len(toks)<m:
        r=random.random()
        if r<0.45:
            toks.append(('U',random.choice([1,2,4,10,28]),1))
        elif r<0.8:
            toks.append(('U',random.choice([1,2]),2*random.randint(1,12)))
        else:
            # U(a,even) V(odd) u
            toks.append(('U',random.choice([1,2]),2*random.randint(1,12)))
            toks.append(('V',2*random.randint(0,12)+1))
            toks.append(('U',1,1))
    if toks[-1][0]!='U' or toks[-1][2]!=1: toks.append(('U',1,1))
    if toks[0][2]>1 and toks[0][1]>2: toks[0]=('U',2,toks[0][2])
    return toks
random.seed(7)
fails=0; ex=[]
for _ in range(400):
    toks=gen()
    res=run(toks,5000000)
    if res[0]!='OK':
        fails+=1
        if len(ex)<8: ex.append((toks,res[:2]))
print('fails',fails,'/400')
for e in ex: print(e)
