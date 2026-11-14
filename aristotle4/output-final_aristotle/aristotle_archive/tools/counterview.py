"""Decode the cells right of the frontier as base-3 digits (3=0, 4=1, 0=2,
most significant digit next to the frontier) every time the head arrives from
the right in state B, and print the decoded value.

Usage: python3 counterview.py <start-step> <count>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3:0, 4:1, 0:2}

START = int(sys.argv[1]); CNT = int(sys.argv[2])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None
prev = pos
n = 0
while n < CNT:
    if m is not None and st == 'B' and prev == pos+1 and steps >= START:
        cells = tape[m+1:pos+1]
        if all(c in DIG for c in cells):
            v = 0
            for c in cells:
                v = 3*v + DIG[c]
            print(f't={steps} len={len(cells)} v={v} cells={"".join(map(str,cells))}'
                  f' rest={"".join(map(str,tape[pos+1:hi+1]))}')
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
