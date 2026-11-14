from sim import M
m=M()
maxpos=0
n=0
while m.t<50000:
    m.step()
    if m.pos>maxpos:
        maxpos=m.pos
        lo,w=m.word()
        print(n,'t=%d pos=%d lo=%d'%(m.t,m.pos,lo), w)
        n+=1
        if n>35: break
