"""A small Turing machine that writes every prime in unary, one blank apart.

Tape layout, every block separated by exactly one blank, blank elsewhere:

    [D] _ [C] _ [out: 1^2 _ 1^3 _ 1^5 _ ...]

* C is the candidate: n ones, left end L, right end fixed at R.
* D is the divisor: d ones with right end at L-2, testing d = n-1 down to 2.
* out is the answer: each prime p as p ones, then one blank.

A round tests d = n-1, n-2, ..., 2 by chunked subtraction: mark D's cells one
at a time (1 -> 2) and, for each mark, mark one cell of C.  When D is fully
marked, unmark it and run another chunk.  If C empties exactly when D does,
d divides n and n is composite.  If C empties in the middle of a chunk, d does
not divide n, so D loses its leftmost cell and the next d is tried.  When D
shrinks to one cell there is nothing left to test and n is prime: C is copied
into the output, then the candidate grows by one and the next round starts.

The candidate grows by blanking C's rightmost cell, shifting the block one
place left and writing a new cell at R, so R and the output never move.

Symbols: '_' blank, '1' unary one, '2' working mark.
"""

BL, ONE, TWO = '_', '1', '2'

R = []
_seen = {}


def rule(q, r, w, m, n):
    key = (q, r)
    assert key not in _seen, 'duplicate rule %s on %r' % (q, r)
    _seen[key] = True
    R.append('%s %s %s %s %s' % (q, r, w, m, n))


# ------------------------------------------------------------------ boot
# C = 11 (n = 2) at cells 0..1, R = 1, output empty.
rule('0', BL, ONE, 'r', 'b1')
rule('b1', BL, ONE, '*', 'r0')

# ------------------------------------- round start: D = copy of C, minus one
# r0 walks left through C to its left end; C is then marked one cell at a
# time and a D cell written per mark, so D grows to n cells.  C is unmarked,
# D loses its leftmost cell (d = n-1) and the test begins.
rule('r0', ONE, ONE, 'l', 'r0')
rule('r0', BL, BL, 'r', 'B0')            # back onto C's left end
rule('B0', ONE, TWO, 'l', 'B1')          # mark one, go write a D cell
rule('B0', TWO, TWO, 'r', 'B0')          # skip cells already marked
rule('B0', BL, BL, 'l', 'B9')            # C fully marked
rule('B1', TWO, TWO, 'l', 'B1')
rule('B1', BL, BL, 'l', 'B2')            # the gap
rule('B2', ONE, ONE, 'l', 'B2')          # left through D
rule('B2', BL, ONE, 'r', 'B3')           # a new leftmost D cell
rule('B3', ONE, ONE, 'r', 'B3')
rule('B3', BL, BL, 'r', 'B0')            # the gap again
rule('B9', TWO, ONE, 'l', 'B9')          # unmark C
rule('B9', BL, BL, 'l', 'B8')
rule('B8', ONE, ONE, 'l', 'B8')
rule('B8', BL, BL, 'r', 'B6')
rule('B6', ONE, BL, '*', 'S0')           # d = n-1, head at cursor-1

# ---------------------------------------------------------- chunk loop
# cursor = leftmost unmarked cell of D; the head waits on cursor-1.
rule('T0', TWO, TWO, 'r', 'T1')
rule('T0', BL, BL, 'r', 'T1')
rule('T1', ONE, TWO, 'r', 'T2')          # mark a divisor cell
rule('T1', BL, BL, '*', 'U1')            # divisor exhausted
rule('T2', ONE, ONE, 'r', 'T2')          # right through D
rule('T2', BL, BL, 'r', 'T3')            # the gap
rule('T3', TWO, TWO, 'r', 'T3')          # through C's marks
rule('T3', ONE, TWO, 'l', 'T4')          # consume one cell of C
rule('T3', BL, BL, '*', 'F1')            # C ran out mid-chunk
rule('T4', TWO, TWO, 'l', 'T4')
rule('T4', ONE, ONE, 'l', 'T4')
rule('T4', BL, BL, 'l', 'T5')            # the gap
rule('T5', ONE, ONE, 'l', 'T5')          # left through D
rule('T5', TWO, TWO, '*', 'T0')          # on the last mark

# ---------------------------------------------------------- chunk end
# head on the cursor (a blank), D fully marked: unmark D, then look at C.
rule('U1', BL, BL, 'l', 'U2')
rule('U2', TWO, ONE, 'l', 'U2')          # unmark D
rule('U2', BL, BL, 'r', 'U3')
rule('U3', ONE, ONE, 'r', 'U3')
rule('U3', BL, BL, 'r', 'U4')            # the gap
rule('U4', TWO, TWO, 'r', 'U5')          # C marked here
rule('U4', ONE, ONE, 'l', 'U6a')         # C has cells: another chunk
rule('U5', TWO, TWO, 'r', 'U5')
rule('U5', ONE, ONE, 'l', 'U6c')         # unmarked cell: another chunk
rule('U5', BL, BL, '*', 'X1')            # C empty: d divides n
rule('U6c', TWO, TWO, 'l', 'U6c')        # back to C's left end
rule('U6c', BL, BL, 'l', 'U6')           # the gap
rule('U6a', BL, BL, 'l', 'U6')           # the gap
rule('U6', ONE, ONE, 'l', 'U6')
rule('U6', BL, BL, '*', 'T0')            # back to the cursor

# ---------------------------------------------------------- d fails
rule('F1', BL, BL, 'l', 'F2')
rule('F2', TWO, ONE, 'l', 'F2')          # unmark C
rule('F2', ONE, ONE, 'l', 'F2')
rule('F2', BL, BL, 'l', 'F2b')           # the gap
rule('F2b', ONE, ONE, 'l', 'F2b')        # through D
rule('F2b', TWO, ONE, 'l', 'F2b')
rule('F2b', BL, BL, 'r', 'F3')           # D's left end
rule('F3', ONE, BL, '*', 'S0')           # drop D's leftmost cell

# ---------------------------------------------------------- size check
rule('S0', BL, BL, 'r', 'S1')
rule('S1', ONE, ONE, 'r', 'S2')
rule('S1', BL, BL, '*', 'P0')            # D empty: prime
rule('S2', ONE, ONE, 'l', 'S3')
rule('S2', BL, BL, '*', 'P0')            # one cell: prime
rule('S3', ONE, ONE, 'l', 'T0')          # two or more: test

# ---------------------------------------------------------- composite
rule('X1', BL, BL, 'l', 'X2')
rule('X2', TWO, ONE, 'l', 'X2')          # unmark C
rule('X2', BL, BL, 'l', 'X3')
rule('X3', ONE, BL, 'l', 'X3')           # delete D
rule('X3', BL, BL, 'r', 'X4')
rule('X4', BL, BL, 'r', 'X4')
rule('X4', ONE, ONE, '*', 'G0')          # to C's left end

# ---------------------------------------------------------- prime
# P0/P1 reach C's left end; P2a copies its first cell (the one that opens a
# new output block, so it goes one cell past the blank), P2b the rest.
rule('P0', ONE, ONE, 'r', 'P0')          # right through D
rule('P0', BL, BL, 'r', 'P1')
rule('P1', BL, BL, 'r', 'P1')            # over blanks
rule('P1', ONE, ONE, '*', 'P2a')         # C's left end
rule('P2a', ONE, TWO, 'r', 'P3F')        # copy the block's first cell
rule('P2a', TWO, TWO, 'r', 'P2b')
rule('P2b', TWO, TWO, 'r', 'P2b')        # skip copied cells
rule('P2b', ONE, TWO, 'r', 'P3')         # copy this cell
rule('P2b', BL, BL, '*', 'X1')           # C fully copied
rule('P3', ONE, ONE, 'r', 'P3')          # to the output's end
rule('P3', TWO, TWO, 'r', 'P3')
rule('P3', BL, BL, 'r', 'P4')
rule('P4', ONE, ONE, 'r', 'P3')          # a blank inside the output
rule('P4', TWO, TWO, 'r', 'P3')
rule('P4', BL, BL, 'l', 'PW')            # two blanks: the end
rule('P3F', ONE, ONE, 'r', 'P3F')
rule('P3F', TWO, TWO, 'r', 'P3F')
rule('P3F', BL, BL, 'r', 'P4F')
rule('P4F', ONE, ONE, 'r', 'P3F')
rule('P4F', TWO, TWO, 'r', 'P3F')
rule('P4F', BL, BL, '*', 'PW')           # one further: leave the gap
rule('PW', BL, ONE, 'l', 'P5')           # write one cell
rule('P5', ONE, ONE, 'l', 'P5')
rule('P5', BL, BL, 'l', 'P5')
rule('P5', TWO, TWO, 'l', 'P6')          # first mark is C's right end
rule('P6', TWO, TWO, 'l', 'P6')
rule('P6', BL, BL, 'r', 'P2a')

# ---------------------------------------------------------- grow C by one
rule('G0', ONE, ONE, 'r', 'G0')          # to C's right end
rule('G0', BL, BL, 'l', 'G1')
rule('G1', ONE, BL, 'l', 'G2')           # blank R
rule('G2', ONE, ONE, 'l', 'G2')
rule('G2', BL, ONE, 'r', 'G3')           # new cell at the left
rule('G3', ONE, ONE, 'r', 'G3')
rule('G3', BL, ONE, 'l', 'r0')           # new cell at R


def machine():
    return '\n'.join(R) + '\n'


if __name__ == '__main__':
    print('rules', len(R), 'states', len({r.split()[0] for r in R}))
