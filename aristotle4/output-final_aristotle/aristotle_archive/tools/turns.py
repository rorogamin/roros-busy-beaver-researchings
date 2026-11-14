"""Print the tape at every turnaround of the head (direction change).

Usage: python3 turns.py <start-step> <count-of-turns> [L|R|both]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); CNT = int(sys.argv[2])
WHICH = sys.argv[3] if len(sys.argv) > 3 else 'both'
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
lastd = 1
n = 0
while True:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    if d != lastd and steps >= START:
        tag = 'RL' if d == -1 else 'LR'
        if WHICH == 'both' or (WHICH == 'L' and d == -1) or (WHICH == 'R' and d == 1):
            out = []
            for i in range(lo-1, hi+2):
                out.append(('[' + st + ']' if i == pos else '') + str(tape[i]))
            print(f't={steps} {tag} {"".join(out)}')
            n += 1
            if n >= CNT:
                sys.exit()
    lastd = d
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
