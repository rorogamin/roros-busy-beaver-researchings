"""At every long cascade, print the state of the ternary counter.

A cascade is a maximal run of leftward A-moves (gaps of at most 8 steps).  At
the moment a cascade starts the head is at the right end of the used tape, so
the counter is settled: the cells from the frontier rightwards that hold `3`,
`4` or `0` are exactly its digits (`3=0`, `4=1`, `0=2`, most significant next to
the frontier).  Printed for every cascade of length >= MINLEN:

    the time, the counter length L and value v, v/3^L, the number of cells
    between the counter and the right end, the starting and ending cell of the
    cascade (measured from the frontier) and the number of counter increments
    since the previous cascade.

Usage: python3 cascade_counter.py <step-limit> [<min-length>]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3:0, 4:1, 0:2}

LIMIT = int(sys.argv[1])
MINLEN = int(sys.argv[2]) if len(sys.argv) > 2 else 10
N = 8000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None
cst = None; cmin = None; clast = None; cinfo = None
prev_v = None

def counter():
    i = m+1
    v = 0
    n = 0
    while i <= hi and tape[i] in DIG:
        v = 3*v + DIG[tape[i]]
        i += 1
        n += 1
    return n, v, i

def report():
    global prev_v
    L, v, right = cinfo
    d = '' if prev_v is None else f' dv={v-prev_v}'
    prev_v = v
    print(f'casc t={clast} L={L} v={v} v/3^L={v/3**L:.4f} gap={hi-right+1} '
          f'start={cst-m} end={cmin-m} len={cst-cmin}{d}')

while steps < LIMIT:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    if st == 'A' and d == -1 and m is not None:
        if clast is None or steps - clast > 8:
            if cst is not None and cst - cmin >= MINLEN:
                report()
            cst = pos; cmin = pos
            cinfo = counter()
        cmin = min(cmin, pos-1)
        clast = steps
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if w == 1 and (m is None or pos-d < m):
        m = pos-d
        cst = None; clast = None
if cst is not None and cmin is not None and cst - cmin >= MINLEN:
    report()
