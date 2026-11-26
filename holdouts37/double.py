"""Rung 5: exact doubling, growth read off the tape.

The machine never stores a step length anywhere.  A pass copies the band one
cell at a time: mark the first un-copied cell, shuttle to the right end, drop a
fresh cell there, shuttle back to the next un-copied cell.  So the number of
cells added in a pass is whatever the pass finds, and the width goes
1, 2, 4, 8, ...  A wall marker stops the last pass dead: the machine halts.

Symbols: '_' blank, '0' left anchor, '9' band, '1' copied-this-pass,
'2' appended-this-pass, '3' wall.  Band rules are emitted last so '9' takes
the top of the renderer's grey ramp and the band paints white.

States: A find next source, B shuttle out and append, C shuttle back,
N normalise, R return home.
"""

WALL = 64
ANCHOR, BAND, MARK, NEW, BLOCK = '0', '9', '1', '2', '3'


def machine():
    R = ['A %s %s r A' % (MARK, MARK),
         'A %s %s r B' % (BAND, MARK),
         'B %s _ r halt' % BLOCK,
         'B _ %s l C' % NEW,
         'B %s %s r B' % (MARK, MARK),
         'B %s %s r B' % (NEW, NEW),
         'C %s %s l C' % (MARK, MARK),
         'C %s %s l C' % (NEW, NEW),
         'C %s %s r B' % (BAND, MARK),
         'C %s %s r N' % (ANCHOR, ANCHOR),
         'N %s %s r N' % (MARK, BAND),
         'N %s %s r N' % (NEW, BAND),
         'N %s %s l R' % (BLOCK, BLOCK),
         'N _ _ l R',
         'R %s %s r A' % (ANCHOR, ANCHOR)]
    # the band's own rules last: '9' ends up as the final symbol index
    R += ['B %s %s r B' % (BAND, BAND), 'R %s %s l R' % (BAND, BAND), 'N %s %s r N' % (BAND, BAND)]
    R.sort(key=lambda line: BAND in line)
    return '\n'.join(R) + '\n'


def start_tape():
    cells = {0: BAND, WALL: BLOCK}
    right = ''.join(cells.get(c, '_') for c in range(0, WALL + 2))
    return ANCHOR + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('double.txt', 'w').write(text)
    s = Session(0, None, morphett=text, init=start_tape())
    i = s.advance(1000000)
    print('halted', i['halted'], 'step', i['step'], 'cells', i['ones'],
          'span', i['lo'], i['hi'], 'symbols', s.symbols)
    draw(s.snapshot()).save('double.png')
