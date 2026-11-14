"""Print the tape cells near the frontier at every crossing of a fixed line.

Usage: python3 linecross.py <start-step> <line-offset> <count> [<width>]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); LINE = int(sys.argv[2]); CNT = int(sys.argv[3])
W = int(sys.argv[4]) if len(sys.argv) > 4 else 20
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None; prev = pos; n = 0
while n < CNT:
    if m is not None and steps >= START and prev == m+LINE+1 and pos == m+LINE:
        print(f't={steps} {st} {"".join(map(str, tape[m:m+W]))}')
        n += 1
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    prev = pos
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if w == 1 and (m is None or prev < m):
        m = prev
