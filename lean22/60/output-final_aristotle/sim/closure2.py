import random
exec(open('closure.py').read().split('random.seed')[0])
def trial(gen,N=400,seed=2):
    random.seed(seed); fails=0; ex=[]
    for _ in range(N):
        toks=gen()
        if toks is None: continue
        res=run(toks,3000000)
        if res[0]!='OK':
            fails+=1
            if len(ex)<6: ex.append((toks,res[:2]))
    return fails,ex
def mk(bset,cset,aset,maxm=6):
    def g():
        m=random.randint(1,maxm); toks=[]; prevV=False
        for i in range(m):
            if not prevV and i>0 and random.random()<0.3:
                toks.append(('V',random.choice(cset))); prevV=True
            else:
                toks.append(('U',random.choice(aset),random.choice(bset))); prevV=False
        if toks[-1][0]=='V': toks.append(('U',1,1))
        return toks
    return g
print('b in {1,even}, c odd, a any 1..5:', trial(mk([1,2,4,6,8],[1,3,5,7],[1,2,3,4,5]))[0])
print('b in {1,even}, c odd, a in {1,2,4}:', trial(mk([1,2,4,6,8],[1,3,5,7],[1,2,4]))[0])
f,ex=trial(mk([1,2,4,6,8],[1,3,5,7],[1,2,4]))
for e in ex: print(e)
