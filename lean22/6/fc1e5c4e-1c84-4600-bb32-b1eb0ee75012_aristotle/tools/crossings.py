T={('A',0):(1,'R','B'),('A',1):(4,'R','A'),('A',2):(1,'L','A'),('A',3):(4,'R','B'),('A',4):(2,'L','A'),
   ('B',0):(2,'L','B'),('B',1):(3,'L','A'),('B',2):(1,'R','B'),('B',3):(2,'R','A')}
import sys
tape={};pos=0;st='A';steps=0
N=int(sys.argv[1])
cuts=range(-3,5)
seq={c:[] for c in cuts}
while steps<N:
    s=tape.get(pos,0)
    if (st,s) not in T: print("HALT",steps);break
    w,d,ns=T[(st,s)];tape[pos]=w
    if d=='R':
        if pos+1 in seq: seq[pos+1].append(ns+'>')
        pos+=1
    else:
        if pos in seq: seq[pos].append('<'+ns)
        pos-=1
    st=ns;steps+=1
for c in cuts:
    print(c, ' '.join(seq[c][:120]))
