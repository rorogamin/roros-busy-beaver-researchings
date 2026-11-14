"""Print the tape word at each epoch (each time the frontier 1 moves one cell left).

At that moment the whole tape is  0^inf 1 [B] 3 u 0^inf  and the word u over
{2,3,4} determines the entire configuration.  Usage:
    python3 epochwords.py <step-limit>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

LIMIT = int(sys.argv[1])
N = 5000
tape = [0]*N
pos = N//2
st = 'A'
lo = hi = pos
steps = 0
m = None
ep = 0
while steps < LIMIT:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if w == 1 and (m is None or pos-d < m):
        m = pos-d
        ep += 1
        u = ''.join(str(x) for x in tape[pos+1:hi+1])
        print(f'ep={ep} t={steps} st={st} cur={tape[pos]} len={len(u)} u={u}')
        sys.stdout.flush()
print('end', steps)
