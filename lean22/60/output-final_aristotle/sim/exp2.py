from sim import M
m=M()
minpos=0
n=0
while m.t<200000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        lo,w=m.word()
        print(n,'t=%d pos=%d'%(m.t,m.pos), w)
        n+=1
        if n>40: break
