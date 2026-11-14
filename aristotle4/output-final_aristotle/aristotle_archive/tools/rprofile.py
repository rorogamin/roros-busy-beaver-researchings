"""Statistics of the region right of the ternary counter: for each cell offset,
how often does it change from one full-length counter visit to the next?

Usage: python3 rprofile.py <start-step> <count>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3:0, 4:1, 0:2}

START = int(sys.argv[1]); CNT = int(sys.argv[2])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None; prev = pos
rows = []
maxL = 0
while len(rows) < CNT:
    if m is not None and st == 'B' and prev == pos+1 and steps >= START:
        cells = tape[m+1:pos+1]
        if all(c in DIG for c in cells):
            if len(cells) >= maxL:
                if len(cells) > maxL:
                    maxL = len(cells); rows = []
                rows.append((steps, tuple(tape[pos+1:hi+1])))
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

print('counter length', maxL, 'rows', len(rows))
width = min(len(r[1]) for r in rows)
for j in range(width):
    col = [r[1][j] for r in rows]
    ch = sum(1 for a, b in zip(col, col[1:]) if a != b)
    vals = sorted(set(col))
    print(f'cell {j:3d}: changes {ch:5d} / {len(col)-1}  values {vals}')
