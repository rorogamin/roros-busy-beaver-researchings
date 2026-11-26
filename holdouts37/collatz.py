"""A Turing machine that runs the genuine Collatz 3x+1 map, cell by cell.

The tape holds the number in unary, fenced by walls:  [0] 1 1 1 ... 1 [3].
Each cycle the machine counts the cells to find n mod 2, then either

    even:  delete every second 1                  (n -> n/2)
    odd:   copy the block twice, append one 1     (n -> 3n+1)

and halts the moment the count reaches 1.  So it halts exactly when the Collatz
iteration of its start value reaches 1; whether it halts from *every* start
value is the open 3x+1 conjecture.  The tape is bi-infinite (the left wall
never has to exist).

Symbols: '0' left wall, '1' a cell of the number, '2' counted / copy-one mark,
'5' copy-two mark, '6' appended copy, '3' right wall.
States: 10/11/12/13 parity scan, 21/30/31/32 halving, 45/46/50-55 copy one and
copy two, 60-63 the second copy, 70-72 the +1, 80/81 clean up, 40 walk home.
"""

MARK1, MARK2, NEW = '2', '5', '6'


def machine():
    R = []
    a = R.append

    # --- cycle start: standing on the left wall
    a('0 0 0 r 10')

    # --- parity scan: mark every counted cell, remember only n mod 2
    a('10 _ _ r 10')
    a('10 1 2 r 12')          # one counted
    a('12 _ _ r 12')
    a('12 1 2 r 13')          # two counted
    a('13 _ _ r 13')
    a('13 1 2 r 11')          # three counted
    a('11 _ _ r 11')
    a('11 1 2 r 13')          # four, ...
    for st in ('10', '12', '13', '11'):
        for s in ('5', '6'):
            a('%s %s %s r %s' % (st, s, s, st))
    a('10 3 3 l halt')        # empty block: n = 0
    a('12 3 3 l halt')        # exactly one cell: n = 1, done
    a('13 3 3 l 21')          # even -> halve
    a('11 3 3 l 22')          # odd  -> 3n+1

    # --- halve: walk home, then delete every second cell
    for s in ('1', '2', '5', '6', '_'):
        a('21 %s %s l 21' % (s, s))
    a('21 0 0 r 30')
    for s in ('_',):
        a('30 %s %s r 30' % (s, s))
        a('31 %s %s r 31' % (s, s))
        a('32 %s %s r 32' % (s, s))
    for s in ('1', '2', '5', '6'):
        a('30 %s 1 r 31' % s)          # keep the first of each pair
        a('31 %s _ r 32' % s)          # drop the second
        a('32 %s 1 r 31' % s)          # keep the next first
    a('32 3 3 l 40')
    for s in ('1', '2', '5', '6', '_'):
        a('40 %s %s l 40' % (s, s))
    a('40 0 0 * 0')

    # --- 3n+1: home, unmark, copy the block twice, add one
    for s in ('1', '2', '5', '6', '_'):
        a('22 %s %s l 22' % (s, s))
    a('22 0 0 r 45')
    for s in ('1', '_', '5', '6'):
        a('45 %s %s r 45' % (s, s))
    a('45 2 1 r 45')                    # unmark the parity scan
    a('45 3 3 l 46')
    for s in ('1', '2', '5', '6', '_'):
        a('46 %s %s l 46' % (s, s))
    a('46 0 0 r 50')

    # copy one: every original cell is marked and one copy appended at the end
    a('50 _ _ r 50')
    for s in ('2', '5', '6'):
        a('50 %s %s r 50' % (s, s))
    a('50 1 2 r 51')
    a('50 3 3 l 55')
    for s in ('1', '2', '5', '6', '_'):
        a('51 %s %s r 51' % (s, s))
    a('51 3 6 r 52')
    a('52 _ 3 l 53')
    for s in ('1', '2', '5', '6', '_'):
        a('53 %s %s l 53' % (s, s))
    a('53 0 0 r 50')
    for s in ('1', '2', '5', '6', '_'):
        a('55 %s %s l 55' % (s, s))
    a('55 0 0 r 60')

    # copy two: every copy-one mark is marked again and one copy appended
    a('60 _ _ r 60')
    for s in ('1', '5', '6'):
        a('60 %s %s r 60' % (s, s))
    a('60 2 5 r 61')
    a('60 3 3 l 70')
    for s in ('1', '2', '5', '6', '_'):
        a('61 %s %s r 61' % (s, s))
    a('61 3 6 r 62')
    a('62 _ 3 l 63')
    for s in ('1', '2', '5', '6', '_'):
        a('63 %s %s l 63' % (s, s))
    a('63 0 0 r 60')

    # the +1, then turn every mark and copy back into a plain cell
    for s in ('1', '2', '5', '6', '_'):
        a('70 %s %s r 70' % (s, s))
    a('70 3 6 r 71')
    a('71 _ 3 l 72')
    for s in ('1', '2', '5', '6', '_'):
        a('72 %s %s l 72' % (s, s))
    a('72 0 0 r 80')
    for s in ('1', '_'):
        a('80 %s %s r 80' % (s, s))
    for s in ('2', '5', '6'):
        a('80 %s 1 r 80' % s)
    a('80 3 3 l 81')
    for s in ('1', '2', '5', '6', '_'):
        a('81 %s %s l 81' % (s, s))
    a('81 0 0 * 0')

    R.sort(key=lambda line: line.split()[2] == '1')
    return '\n'.join(R) + '\n'


def start_tape(n):
    return '*0' + '1' * n + '3'


def reference(n):
    seq = [n]
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        seq.append(n)
    return seq


def run(text, n, limit=20_000_000):
    """Step the rule table directly and record the count at every cycle start."""
    T = {}
    for line in text.splitlines():
        st, rd, wr, mv, nx = line.split()
        T[(st, rd)] = (wr, {'l': -1, 'r': 1, '*': 0, 'n': 0}[mv], nx)
    tape = {i: s for i, s in enumerate('0' + '1' * n + '3')}
    head, state, counts, prev = 0, '0', [], None
    for step in range(limit):
        if state == '0' and prev != '0':
            counts.append(sum(1 for v in tape.values() if v == '1'))
        prev = state
        r = T.get((state, tape.get(head, '_')))
        if r is None:
            return 'crash', step, counts
        wr, d, nx = r
        if wr == '_':
            tape.pop(head, None)
        else:
            tape[head] = wr
        head += d
        if nx == 'halt':
            return 'halt', step, counts
        state = nx
    return 'timeout', limit, counts


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('collatz.txt', 'w').write(text)
    n = 7
    kind, step, counts = run(text, n)
    print('start', n, kind, 'step', step, 'rules', len(text.splitlines()))
    print('machine says ', counts)
    print('collatz says ', reference(n))
    print('match', counts == reference(n))
    s = Session(0, None, morphett=text, init=start_tape(n))
    i = s.advance(200000)
    print('sim halted', i['halted'], 'step', i['step'], 'cells', i['ones'],
          'span', i['lo'], i['hi'])
    draw(s.snapshot()).save('collatz.png')
