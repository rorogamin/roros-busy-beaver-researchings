"""Rung 4: one run, three lobes whose rims advance 1, 2 and 3 cells per pass,
each lobe nested inside the last, and the third lobe halts on its wall.

Tape symbols (deliberately few): '_' blank, '0' fixed left rim, '1' rim (all
lobes share it, the state says which lobe is running), '2' wall, '9' fill.
Rules that mention the fill are emitted last: the renderer numbers symbols in
order of first appearance, so '9' gets the top of the grey ramp and the body of
each wedge paints white.

States: 0/40/50 sweep out (lobes 1/2/3), 10/20+21/30+31+32 rim handling with
growth 1/2/3, 11/22/33 return, 60/62 close a lobe and hand over.
"""

WALLS = (120, 240, 360)
LEFT, RIM, WALL, FILL = '0', '1', '2', '9'
EVERY = ('_', LEFT, RIM, WALL, FILL)
TRAVEL = ('_', RIM, WALL, FILL)      # cells a walking state steps over


def machine():
    R = []
    # --- closers: walk home, then drop the next lobe's rim on the first cell
    for q, nxt, ret in ((60, 41, 40), (62, 51, 50)):
        for s in TRAVEL:
            R.append('%d %s %s l %d' % (q, s, s, q))
        R.append('%d %s %s r %d' % (q, LEFT, LEFT, q + 1))
        R.append('%d _ %s l %d' % (q + 1, RIM, nxt))
        R.append('%d %s %s l %d' % (q + 1, FILL, RIM, nxt))
    R += ['41 %s %s l 41' % (s, s) for s in TRAVEL] + ['41 %s %s r 40' % (LEFT, LEFT)]
    R += ['51 %s %s l 51' % (s, s) for s in TRAVEL] + ['51 %s %s r 50' % (LEFT, LEFT)]
    # --- returns to the sweep of the lobe that is running
    for ret, sweep in ((11, 0), (22, 40), (33, 50)):
        R += ['%d %s %s l %d' % (ret, s, s, ret) for s in TRAVEL]
        R.append('%d %s %s r %d' % (ret, LEFT, LEFT, sweep))
    # --- rim handling: erase the rim, walk g-1 cells, write it again
    R += ['10 _ 1 l 11', '10 %s 1 l 11' % FILL, '10 %s _ l 60' % WALL]
    R += ['20 %s _ l 62' % WALL, '20 _ _ r 21', '20 %s _ r 21' % FILL,
          '21 %s _ l 62' % WALL, '21 _ 1 l 22', '21 %s 1 l 22' % FILL]
    R += ['30 %s _ r halt' % WALL, '30 _ _ r 31', '30 %s _ r 31' % FILL,
          '31 %s _ r halt' % WALL, '31 _ _ r 32', '31 %s _ r 32' % FILL,
          '32 %s _ r halt' % WALL, '32 _ 1 l 33', '32 %s 1 l 33' % FILL]
    # --- sweeps: paint, stop on the rim, hand over to that lobe's handler
    for sweep, handler in ((0, 10), (40, 20), (50, 30)):
        R += ['%d _ %s r %d' % (sweep, FILL, sweep),
              '%d %s %s r %d' % (sweep, FILL, FILL, sweep),
              '%d %s _ r %d' % (sweep, RIM, handler)]
    # fill rules last, so '9' is the last symbol the parser meets
    R.sort(key=lambda line: FILL in line)
    return '\n'.join(R) + '\n'


def start_tape():
    cells = {1: RIM, WALLS[0]: WALL, WALLS[1]: WALL, WALLS[2]: WALL}
    right = ''.join(cells.get(c, '_') for c in range(0, WALLS[2] + 2))
    return LEFT + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('wedge.txt', 'w').write(text)
    s = Session(0, None, morphett=text, init=start_tape())
    i = s.advance(400000)
    print('halted', i['halted'], 'step', i['step'], 'ones', i['ones'],
          'span', i['lo'], i['hi'], 'rules', len(text.splitlines()),
          'symbols', s.symbols)
    draw(s.snapshot()).save('wedge.png')
