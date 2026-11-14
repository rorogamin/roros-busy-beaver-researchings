"""Test the hypothesis that the region to the right of a `3` marker is a binary
counter with two cells per digit, `4 2` = 0 and `4 4` = 1, least significant
digit first, and that every bounce of the returning sweep off a `3` increments
it by one.

A "bounce" is the transition B3 -> 4RA: the head, sweeping left in state B,
meets a cell holding 3, rewrites it as 4 and goes right again.

For every bounce we print the cells to the right of the marker, their reading as
a binary number if they have the shape (4 2 | 4 4)*, and the difference to the
previous reading at the same marker position.

Usage: python3 bincounter.py <start-step> <how-many-bounces>
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

START = int(sys.argv[1])
CNT = int(sys.argv[2])

N = 8000
tape = [0] * N
pos = N // 2
st = 'A'
steps = 0
hi = pos
printed = 0
last = {}


def read_pairs(cells):
    """value of the cells read as binary digits, two cells per digit,
    4 2 = 0 and 4 4 = 1, least significant digit first; None if the shape is
    wrong"""
    v = 0
    k = 0
    for i in range(0, len(cells) - 1, 2):
        a, b = cells[i], cells[i + 1]
        if a != 4 or b not in (2, 4):
            return None, k
        if b == 4:
            v += 1 << k
        k += 1
    return v, k


while printed < CNT:
    s = tape[pos]
    t = T[(st, s)]
    if t is None:
        print('HALT', steps)
        break
    if st == 'B' and s == 3 and steps >= START:
        cells = tape[pos + 1:hi + 1]
        v, k = read_pairs(cells)
        prev = last.get(pos)
        d = None if (v is None or prev is None) else v - prev
        last[pos] = v
        print(f't={steps} marker={pos - N // 2} digits={k} value={v} delta={d} '
              f'| {"".join(map(str, cells[:24]))}')
        printed += 1
    w, d_, ns = t
    tape[pos] = w
    pos += d_
    st = ns
    steps += 1
    hi = max(hi, pos)
