"""Record the ternary counter value at every extension of the tape to the right.

Usage: python3 births.py <step-limit>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3:0, 4:1, 0:2}

LIMIT = int(sys.argv[1])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None; prev = pos
v = None; L = None
while steps < LIMIT:
    if m is not None and st == 'B' and prev == pos+1:
        cells = tape[m+1:pos+1]
        if all(c in DIG for c in cells) and len(cells) >= (L or 0):
            x = 0
            for c in cells:
                x = 3*x + DIG[c]
            v = x; L = len(cells)
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    grow = (d == 1 and pos == hi)
    prev = pos
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if grow:
        print(f'grow t={steps} rightend={hi-m if m else None} L={L} v={v}')
    if w == 1 and (prev < (m if m is not None else 10**9)):
        m = prev
        L = None
        print(f'--- epoch t={steps} width={hi-lo+1}')
