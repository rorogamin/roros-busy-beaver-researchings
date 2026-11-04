import sys
sys.path.insert(0, 'tools')
from verify_epsilon1_tm import TM_TABLE

tape = {}
pos, st = 0, 'A'
trace = []
mark = []
for i in range(400):
    r = tape.get(pos, 0)
    w, d, nx = TM_TABLE[st][r]
    tape[pos] = w
    pos += 1 if d == 'R' else -1
    prev, st = st, nx
    trace.append(f'{prev}{r}->{w}{"L" if d=="L" else "R"}=>{nx}@{pos}')
    if nx == 'D' and prev == 'C':
        mark.append(i + 1)
print('first C->D edges (step indices):', mark[:10])
# print trace around the first C->D
j = mark[0] if mark else len(trace)
print('trace[-60:]:')
print(' '.join(trace[max(0, j-60):j]))
# then continue 200 more steps
cont = []
for i in range(j, min(j + 250, 400)):
    pass
print('\nraw cells near origin after first C->D:', {k: v for k, v in sorted(tape.items()) if k < 30 and v})
