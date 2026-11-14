from sim import M
def parse(m,start):
    i=start; js=[]
    lo,hi=m.bounds()
    while i<=hi:
        if m.tape.get(i,0)!=0: return None
        i+=1; j=0
        while m.tape.get(i,0)==4: j+=1; i+=1
        if m.tape.get(i,0)!=2: return None
        i+=1; js.append(j)
    return js
m=M()
minpos=0
n=0
res=[]
while m.t<3000000:
    m.step()
    if m.pos<minpos:
        minpos=m.pos
        if m.st=='A':
            js=parse(m,m.pos)
            if js is not None:
                res.append((m.t,m.pos,js))
for t,p,js in res[:40]:
    print(t,p,js)
print(len(res))
