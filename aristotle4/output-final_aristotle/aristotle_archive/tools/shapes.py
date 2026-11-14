"""How often does the run-length *shape* of the whole tape repeat?

Prints, for a window of steps, the shape signature (state, direction, the
sequence of block symbols of the tape with the head's block marked) whenever it
is one that has been seen before, together with the exponent vector.

Usage: python3 shapes.py <start> <end> [<print-count>]
"""
import sys
from collections import defaultdict

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); END = int(sys.argv[2])
PC = int(sys.argv[3]) if len(sys.argv) > 3 else 60
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
seen = defaultdict(list)
printed = 0
while steps < END:
    if steps >= START:
        # run-length encode tape[lo-1 .. hi+1]
        blocks = []
        hb = None
        for i in range(lo-1, hi+2):
            s = tape[i]
            if blocks and blocks[-1][0] == s:
                blocks[-1][1] += 1
            else:
                blocks.append([s, 1])
            if i == pos:
                hb = (len(blocks)-1, blocks[-1][1]-1)   # block index, offset in block
        sig = (st, tuple(b[0] for b in blocks), hb[0], hb[1] if hb[1] < 2 else 'k',
               len(blocks) - hb[0])
        exps = tuple(b[1] for b in blocks)
        prev = seen[sig]
        if prev and printed < PC:
            pt, pe = prev[-1]
            if len(pe) == len(exps):
                d = tuple(a-b for a, b in zip(exps, pe))
                print(f't={steps} dt={steps-pt} sig={sig[1]} hb={hb} exps={exps} delta={d}')
                printed += 1
        seen[sig].append((steps, exps))
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
