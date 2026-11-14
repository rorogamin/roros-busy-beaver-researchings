"""Print, at every arrival of the head from the right in state B on the ternary
counter, the ternary counter value (cells right of the frontier, 3=0 4=1 0=2,
MSD next to the frontier) and the binary decoding of the region to the right of
the head (2=0, 4=1, least significant cell first, stopping at the first cell
that is neither 2 nor 4).

Usage: python3 twovals.py <start-step> <count>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3:0, 4:1, 0:2}
BIT = {2:0, 4:1}

START = int(sys.argv[1]); CNT = int(sys.argv[2])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None
prev = pos
n = 0
lastv = None
while n < CNT:
    if m is not None and st == 'B' and prev == pos+1 and steps >= START:
        cells = tape[m+1:pos+1]
        if all(c in DIG for c in cells):
            v = 0
            for c in cells:
                v = 3*v + DIG[c]
            # binary part
            i = pos+1
            bits = []
            while i <= hi and tape[i] in BIT:
                bits.append(BIT[tape[i]])
                i += 1
            w = 0
            for b in reversed(bits):
                w = 2*w + b
            tail = ''.join(map(str, tape[i:hi+1]))
            print(f't={steps} v={v} nb={len(bits)} w={w} tail={tail}')
            n += 1
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w_, d, ns = t
    prev = pos
    tape[pos] = w_; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if w_ == 1 and (m is None or prev < m):
        m = prev
