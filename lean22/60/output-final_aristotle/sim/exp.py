from sim import M

def blocks(m):
    # parse tape to the right of head as 0 4^j 2 blocks
    lo,hi=m.bounds()
    i=m.pos
    js=[]
    rest=None
    while i<=hi:
        if m.tape.get(i,0)!=0: rest=('nonzero-start',i); break
        i+=1
        j=0
        while m.tape.get(i,0)==4: j+=1; i+=1
        if m.tape.get(i,0)!=2: rest=('no-2',i,j); break
        i+=1
        js.append(j)
    return js,rest

m=M()
n=0
minpos=0
events=[]
while m.t<3000000:
    m.step()
    if m.st=='A' and m.pos<minpos and m.read()==0:
        minpos=m.pos
        js,rest=blocks(m)
        events.append((n,m.t,m.pos,js,rest))
        n+=1
for e in events[:60]:
    print(e[0],'t=',e[1],'pos=',e[2],'js=',e[3],'rest=',e[4])
print(len(events))
