"""Print the raw configuration for a window of steps.

Usage: python3 trace.py <start-step> <count> [<every>]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); CNT = int(sys.argv[2])
EVERY = int(sys.argv[3]) if len(sys.argv) > 3 else 1
N = 5000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0

def show():
    out = []
    for i in range(lo-1, hi+2):
        out.append(('[' + st + ']' if i == pos else '') + str(tape[i]))
    return ''.join(out)

while steps < START + CNT:
    if steps >= START and (steps - START) % EVERY == 0:
        print(f't={steps} {show()}')
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
