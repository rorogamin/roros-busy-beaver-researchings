"""Summary statistics of the round trips of the head (counter visit to counter
visit): number of direction changes ("turns"), maximum reach to the right of the
counter, and number of machine steps.

Usage: python3 tripstats.py <start-step> <how-many-round-trips>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3: 0, 4: 1, 0: 2}

START = int(sys.argv[1])
CNT = int(sys.argv[2])

N = 20000
tape = [0] * N
pos = N // 2
st = 'A'
steps = 0
m = None
prev = pos
lastdir = 0
nturn = 0
reach = 0
base = None
t0 = 0
printed = 0

while printed < CNT:
    if (m is not None and st == 'B' and prev == pos + 1
            and all(c in DIG for c in tape[m + 1:pos + 1])):
        if steps >= START and base is not None:
            v = 0
            for c in tape[m + 1:pos + 1]:
                v = 3 * v + DIG[c]
            print(f'v={v} turns={nturn} reach={reach - base} steps={steps - t0} '
                  f'lsd={tape[pos]}')
            printed += 1
        base = pos
        reach = pos
        nturn = 0
        t0 = steps
    s = tape[pos]
    tr = T[(st, s)]
    if tr is None:
        print('HALT', steps)
        break
    w, d, ns = tr
    if lastdir != 0 and d != lastdir:
        nturn += 1
    lastdir = d
    prev = pos
    tape[pos] = w
    pos += d
    st = ns
    steps += 1
    if pos > reach:
        reach = pos
    if w == 1 and (m is None or prev < m):
        m = prev
