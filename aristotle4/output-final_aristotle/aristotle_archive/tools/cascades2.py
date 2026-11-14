"""Record every long left-moving A-cascade: where it starts, where it dies,
what stops it, and the tape between its death point and the frontier.

Usage: python3 cascades2.py <step-limit> [<min-length>]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

LIMIT = int(sys.argv[1])
MINLEN = int(sys.argv[2]) if len(sys.argv) > 2 else 5
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None
# a cascade = a maximal time interval during which the head, in state A, keeps
# moving left (possibly with short right excursions of <= 2 steps: the P/Q
# automaton takes 3 steps per cell over the 0202 background)
cst = None      # cascade start cell
cmin = None     # leftmost cell reached
clast = None    # last time an A-left move happened
while steps < LIMIT:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    if st == 'A' and d == -1:
        if clast is None or steps - clast > 8:
            # close the previous cascade
            if cst is not None and cst - cmin >= MINLEN:
                print(f'casc t={clast} start={cst-m} end={cmin-m} len={cst-cmin} '
                      f'stop={tape[cmin-1]} tape={"".join(map(str,tape[m:cmin+2]))}')
            cst = pos
            cmin = pos
        cmin = min(cmin, pos-1)
        clast = steps
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if w == 1 and (m is None or pos-d < m):
        m = pos-d
        cst = None; clast = None
