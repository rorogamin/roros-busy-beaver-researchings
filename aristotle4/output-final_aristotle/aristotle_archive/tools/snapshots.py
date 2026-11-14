"""Dump full tape snapshots at structural events.

Events recorded:
  * "birth"   : the head (state A) steps onto the blank cell just right of the
                used region (extension of the tape to the right);
  * "cascade" : a maximal run of consecutive leftward A-moves of length >= 3,
                reported at its start and at its end;
  * "epoch"   : the leftmost 1 (frontier) moves one cell left.

Usage: python3 snapshots.py <step-limit> [<first-event>] [<count>]
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

LIMIT = int(sys.argv[1])
FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 0
CNT = int(sys.argv[3]) if len(sys.argv) > 3 else 40

N = 4000
tape = [0]*N
pos = N//2
st = 'A'
lo = hi = pos
steps = 0
m = None          # frontier position (leftmost 1)
ev = 0

def show(pos, st):
    a = max(lo-1, 0); b = min(hi+1, N-1)
    s = []
    for i in range(a, b+1):
        if i == pos:
            s.append('[' + st + str(tape[i]) + ']')
        else:
            s.append(str(tape[i]))
    return ''.join(s)

def rep(tag, pos, st):
    global ev
    ev += 1
    if ev >= FIRST:
        mm = '' if m is None else f' m={m-lo}'
        print(f'#{ev} {tag} t={steps} w={hi-lo+1}{mm} : {show(pos,st)}')
    if ev >= FIRST + CNT:
        sys.exit()

casc = 0
cstart = None
while steps < LIMIT:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps); break
    w, d, ns = t
    left_A = (st == 'A' and d == -1)
    if left_A:
        if casc == 0:
            cstart = pos
        casc += 1
    else:
        if casc >= 3:
            rep(f'cascade-end len={casc} from={cstart-lo}', pos, st)
        casc = 0
    newcell = (d == 1 and pos == hi and st == 'A')
    tape[pos] = w; pos += d; st = ns; steps += 1
    lo = min(lo, pos); hi = max(hi, pos)
    if newcell:
        rep('birth', pos, st)
    if w == 1 and (m is None or pos-d < m):
        m = pos-d
        rep('epoch', pos, st)
print('end', steps)
