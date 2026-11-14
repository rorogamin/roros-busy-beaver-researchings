"""Print head position vs time (sampled) and the sequence of deep turnarounds.

Usage: python3 profile_pos.py <start> <end> <sample>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); END = int(sys.argv[2]); SAMP = int(sys.argv[3])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
base = N//2
while steps < END:
    if steps >= START and steps % SAMP == 0:
        print(steps, pos-base)
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
