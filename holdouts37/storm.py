"""Bell storm: a bouncer that never settles.  Each lobe grows one cell per pass
until it runs into the next wall, then the machine starts a fresh lobe from the
anchor.  The walls sit at irregular distances drawn from a heavy-tailed
distribution, so the bells come out in every size at once -- a few enormous
ones with thousands of tiny ones packed around them -- and the last wall halts
the machine.

Every pass paints twice: out in tone '9', home in tone '8', so the interior is
a dense two-tone weave rather than a flat fill.

Symbols: '0' anchor, '1' rim, '2' wall, '3' far end (halt), '8'/'9' tones.
States: A sweep out, B drop the advanced rim, R1 walk home, CL close a lobe,
D drop the next lobe's rim.
"""

ANCHOR, RIM, WALL, END = '0', '1', '2', '3'
LOW, HIGH = '8', '9'
EVERY = (LOW, HIGH)


def walls(seed, lobes):
    """Irregular wall positions: mostly tight, with occasional huge gaps."""
    import random
    rnd = random.Random(seed)
    out, x = [], 1
    for _ in range(lobes):
        step = rnd.choice((1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9, 14))
        x += step
        out.append(x)
    return out


def machine():
    R = ['A _ %s r A' % HIGH, 'A %s %s r A' % (HIGH, HIGH), 'A %s %s r A' % (LOW, LOW),
         'A %s _ r B' % RIM, 'A %s %s l halt' % (END, END),
         'B _ %s l R1' % RIM, 'B %s %s l R1' % (HIGH, RIM), 'B %s %s l R1' % (LOW, RIM),
         'B %s _ l CL' % WALL,
         'R1 %s %s l R1' % (HIGH, LOW), 'R1 %s %s l R1' % (LOW, LOW),
         'R1 %s %s l R1' % (RIM, RIM), 'R1 _ _ l R1', 'R1 %s %s r A' % (ANCHOR, ANCHOR),
         'CL %s %s l CL' % (HIGH, LOW), 'CL %s %s l CL' % (LOW, LOW),
         'CL %s %s l CL' % (RIM, RIM), 'CL _ _ l CL', 'CL %s %s r D' % (ANCHOR, ANCHOR),
         'D %s %s l R1' % (HIGH, RIM), 'D %s %s l R1' % (LOW, RIM), 'D _ %s l R1' % RIM]
    R.sort(key=lambda line: HIGH in line)
    return '\n'.join(R) + '\n'


def start_tape(seed=5, lobes=160):
    spots = walls(seed, lobes)
    cells = {1: RIM, spots[-1] + 2: END}
    for p in spots:
        cells[p] = WALL
    width = spots[-1] + 4
    right = ''.join(cells.get(c, '_') for c in range(0, width))
    return ANCHOR + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('storm.txt', 'w').write(text)
    s = Session(0, None, morphett=text, init=start_tape())
    i = s.advance(1000000)
    print('halted', i['halted'], 'step', i['step'], 'painted', i['ones'],
          'span', i['lo'], i['hi'], 'rules', len(text.splitlines()),
          'symbols', s.symbols, 'walls', len(walls(5, 160)))
    draw(s.snapshot()).save('storm.png')
