"""Trace complete round trips of the head (counter visit to counter visit) and
print the zig-zag structure of each trip: the sequence of local extrema of the
head position, measured in cells to the right of the least significant counter
digit.

A "counter visit" is the moment the head arrives from the right, in state B, on
the least significant digit of the ternary counter (the same event as in
region.py).

Usage: python3 roundtrip.py <start-step> <how-many-round-trips>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}
DIG = {3: 0, 4: 1, 0: 2}

START = int(sys.argv[1])
CNT = int(sys.argv[2])

N = 8000
tape = [0] * N
pos = N // 2
st = 'A'
hi = pos
steps = 0
m = None
prev = pos
lastdir = 0
extrema = []
base = None
printed = 0

while printed < CNT:
    # detect a counter visit
    if (m is not None and st == 'B' and prev == pos + 1
            and all(c in DIG for c in tape[m + 1:pos + 1])):
        if steps >= START and base is not None:
            v = 0
            for c in tape[m + 1:pos + 1]:
                v = 3 * v + DIG[c]
            rel = [e - base for e in extrema]
            print(f't={steps} v={v} lsd={tape[pos]} extrema={rel}')
            printed += 1
        base = pos
        extrema = []
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps)
        break
    w, d, ns = t
    if lastdir != 0 and d != lastdir:
        extrema.append(pos)
    lastdir = d
    prev = pos
    tape[pos] = w
    pos += d
    st = ns
    steps += 1
    hi = max(hi, pos)
    if w == 1 and (m is None or prev < m):
        m = prev
