"""Sample the tape (offsets measured from the frontier) every time the head
crosses a fixed line leftwards, and report per-cell change frequencies.

Usage: python3 rprofile2.py <start-step> <line-offset> <count>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1]); LINE = int(sys.argv[2]); CNT = int(sys.argv[3])
N = 6000
tape = [0]*N
pos = N//2; st = 'A'; lo = hi = pos; steps = 0
m = None; prev = pos
rows = []
while len(rows) < CNT:
    if m is not None and steps >= START and prev == m+LINE+1 and pos == m+LINE:
        rows.append((steps, st, tuple(tape[m:hi+1])))
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
        rows = []      # restart the statistics at each new epoch

print('rows', len(rows), 'states', sorted(set(r[1] for r in rows)))
width = min(len(r[2]) for r in rows)
for j in range(width):
    col = [r[2][j] for r in rows]
    ch = sum(1 for a, b in zip(col, col[1:]) if a != b)
    print(f'cell {j:3d}: changes {ch:5d} / {len(col)-1}  values {sorted(set(col))}')
