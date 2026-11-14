import sys
# transitions: (state,sym) -> (write, dir, newstate); dir +1 right, -1 left
T = {
 ('A',0):(1,+1,'B'), ('A',1):(2,-1,'A'), ('A',2):(3,-1,'B'), ('A',3):(4,-1,'B'), ('A',4):None,
 ('B',0):(0,-1,'A'), ('B',1):(4,-1,'B'), ('B',2):(3,+1,'A'), ('B',3):(4,-1,'A'), ('B',4):(0,+1,'B'),
}

class M:
    def __init__(self):
        self.tape = {}
        self.pos = 0
        self.st = 'A'
        self.t = 0
    def read(self): return self.tape.get(self.pos,0)
    def step(self):
        r = T[(self.st,self.read())]
        if r is None: return False
        w,d,s = r
        self.tape[self.pos]=w
        self.pos+=d
        self.st=s
        self.t+=1
        return True
    def bounds(self):
        ks=[k for k,v in self.tape.items() if v!=0]
        if not ks: return (0,0)
        return (min(ks),max(ks))
    def word(self):
        lo,hi=self.bounds()
        lo=min(lo,self.pos); hi=max(hi,self.pos)
        s=''
        for i in range(lo,hi+1):
            if i==self.pos: s+='['+self.st+']'
            s+=str(self.tape.get(i,0))
        return (lo,s)
