"""Macro-machine view of `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`.

The tape is cut into blocks of `k` cells (aligned so that cell `0`, the cell the
machine starts on, is the first cell of a block).  A *macro step* simulates the
machine inside one block from the moment the head enters it until it leaves it
again; a *chain step* runs a whole run of identical blocks at once when the
macro transition leaves the state and the direction unchanged.

Usage: python3 macro.py <blocksize> <macro-step-limit> [<print-every>]
Prints the macro tape in run-length form.
"""
import sys

T = {('A',0):(1,1,'B'),('A',1):None,('A',2):(3,1,'A'),('A',3):(2,-1,'A'),('A',4):(2,1,'B'),
     ('B',0):(2,-1,'B'),('B',1):(3,-1,'A'),('B',2):(4,-1,'B'),('B',3):(4,1,'A'),('B',4):(0,1,'A')}

K = int(sys.argv[1])
LIMIT = int(sys.argv[2])
EVERY = int(sys.argv[3]) if len(sys.argv) > 3 else 1
OFF = int(sys.argv[4]) if len(sys.argv) > 4 else 0

BLANK = tuple([0]*K)
memo = {}

def block_step(st, blk, side):
    """Enter block `blk` in state `st` from `side` ('L' = from the left, head on
    cell 0; 'R' = from the right, head on cell k-1).  Returns
    (new block, new state, exit side, cost) or None if the machine halts."""
    key = (st, blk, side)
    if key in memo:
        return memo[key]
    cells = list(blk)
    p = 0 if side == 'L' else K-1
    s = st
    cost = 0
    while 0 <= p < K:
        tr = T[(s, cells[p])]
        if tr is None:
            memo[key] = None
            return None
        w, d, ns = tr
        cells[p] = w
        p += d
        s = ns
        cost += 1
    res = (tuple(cells), s, 'R' if p == K else 'L', cost)
    memo[key] = res
    return res


class Tape:
    def __init__(self):
        self.left = []    # list of [blk, exp], last one adjacent to the head
        self.right = []   # list of [blk, exp], first one adjacent to the head
        self.st = 'A'
        self.dir = 'R'    # 'R': about to enter right[0] from its left end
        self.steps = 0
        self.macro = 0

    def pop(self, side):
        lst = self.right if side == 'R' else self.left
        if not lst:
            return BLANK, 0
        i = 0 if side == 'R' else len(lst)-1
        blk, e = lst[i]
        return blk, e

    def take(self, side, n):
        lst = self.right if side == 'R' else self.left
        if not lst:
            return
        i = 0 if side == 'R' else len(lst)-1
        lst[i][1] -= n
        if lst[i][1] == 0:
            lst.pop(i)

    def push(self, side, blk, n):
        lst = self.right if side == 'R' else self.left
        i = 0 if side == 'R' else len(lst)-1
        if lst and lst[i][0] == blk:
            lst[i][1] += n
        else:
            if side == 'R':
                lst.insert(0, [blk, n])
            else:
                lst.append([blk, n])

    def step(self):
        src = 'R' if self.dir == 'R' else 'L'
        blk, e = self.pop(src)
        enter = 'L' if self.dir == 'R' else 'R'
        r = block_step(self.st, blk, enter)
        if r is None:
            return 'HALT'
        nb, ns, ex, cost = r
        chain = (ns == self.st and
                 ((self.dir == 'R' and ex == 'R') or (self.dir == 'L' and ex == 'L')))
        n = e if (chain and e > 0) else 1
        if n == 0:
            n = 1
        self.take(src, n)
        if (self.dir == 'R' and ex == 'R') or (self.dir == 'L' and ex == 'L'):
            dst = 'L' if self.dir == 'R' else 'R'
            self.push(dst, nb, n)
            newdir = self.dir
        else:
            self.push(src, nb, n)
            newdir = 'L' if self.dir == 'R' else 'R'
        self.st = ns
        self.dir = newdir
        self.steps += cost * n
        self.macro += 1
        return 'OK'

    def show(self):
        def f(lst):
            return ' '.join(''.join(map(str, b)) + ('^%d' % e if e != 1 else '')
                            for b, e in lst)
        return f(self.left) + f' [{self.st}{self.dir}] ' + f(self.right)


tp = Tape()
if OFF:
    # start the head OFF cells into the first block: simulate those cells
    # inside an initially blank block
    cells = list(BLANK)
    p = OFF
    s = 'A'
    cost = 0
    while 0 <= p < K:
        tr = T[(s, cells[p])]
        w, d, ns = tr
        cells[p] = w
        p += d
        s = ns
        cost += 1
    tp.st = s
    tp.steps = cost
    if p == K:
        tp.left.append([tuple(cells), 1])
        tp.dir = 'R'
    else:
        tp.right.insert(0, [tuple(cells), 1])
        tp.dir = 'L'
while tp.macro < LIMIT:
    if tp.macro % EVERY == 0:
        print(f'm={tp.macro} t={tp.steps} {tp.show()}')
    if tp.step() == 'HALT':
        print(f'HALT at macro {tp.macro}, step {tp.steps}')
        break
print(f'm={tp.macro} t={tp.steps} {tp.show()}')
