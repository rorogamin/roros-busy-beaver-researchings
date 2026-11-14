from sim import M
m=M()
prev=0
dirn=0
lefts=[];rights=[]
while m.t<200000:
    p0=m.pos; m.step(); p1=m.pos
    d=p1-p0
    if dirn!=0 and d!=dirn:
        if d>0: lefts.append((m.t,p0))
        else: rights.append((m.t,p0))
    dirn=d
print('lefts',[p for t,p in lefts[:120]])
print('rights',[p for t,p in rights[:120]])
