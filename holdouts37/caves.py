"""Caves everywhere: a bell whose passes are bitten short at random depths.

A rate tape left of the anchor is read once per pass.  '8' is a full sweep to
the rim (which creeps one cell right); '5', '6' and '7' are stubs of 4, 12 and
24 cells that turn around early.  A stub paints only its own little arc, the
band beyond it stays dark until a later full sweep caps it -- that dark gap is a
cave.  Every pass paints out in one tone and back in the other, so each pass is
a visible row and the caves show as bites out of the fan.  Running out of rate
tape halts the machine.

Symbols: '0' anchor, '1' rim, '3' far end, '4' spent rate cell, '5'/'6'/'7' stub
rates, '8' full pass, '9'/'2' the two paint tones.
States: 0 sweep out, 50/51/53 walk back to the anchor, 60x/61x/62x stubs,
70 full sweep, 71 drop the rim, 72 walk home (repainting), 73 turn.
"""

ANCHOR, RIM, END, SPENT, FILL, ALT = '0', '1', '3', '4', '9', '2'
DEPTH = {'5': 4, '6': 12, '7': 24}
CHAIN = {'5': '60', '6': '61', '7': '62'}
STEPS = 'abcdefghijklmnopqrstuvwx'
FULL = '8'


def machine():
    R = ['0 %s %s l 0' % (SPENT, SPENT), '0 %s %s l 0' % (ANCHOR, ANCHOR),
         '0 _ _ l 0', '0 %s %s l 0' % (FILL, FILL), '0 %s %s l 0' % (ALT, ALT),
         '0 %s %s l halt' % (END, END)]
    for sym, depth in DEPTH.items():
        walk, chain = '5' + sym, CHAIN[sym]
        R += ['0 %s %s r %s' % (sym, SPENT, walk),
              '%s %s %s r %s' % (walk, SPENT, SPENT, walk),
              '%s %s %s r %sa' % (walk, ANCHOR, ANCHOR, chain),
              '%s %s %s r %sa' % (walk, FILL, FILL, chain),
              '%s %s %s r %sa' % (walk, ALT, ALT, chain),
              '%s _ _ r %sa' % (walk, chain)]
        for k in range(1, depth + 1):
            cur = '%s%s' % (chain, STEPS[k - 1])
            nxt = '%s%s' % (chain, STEPS[k]) if k < depth else '73'
            R += ['%s _ %s r %s' % (cur, FILL, nxt),
                  '%s %s %s r %s' % (cur, FILL, FILL, nxt),
                  '%s %s %s r %s' % (cur, ALT, FILL, nxt),
                  '%s %s %s l 72' % (cur, RIM, RIM),
                  '%s %s %s l halt' % (cur, END, END)]
    R += ['0 %s %s r 53' % (FULL, SPENT),
          '53 %s %s r 53' % (SPENT, SPENT),
          '53 %s %s r 70' % (ANCHOR, ANCHOR),
          '53 %s %s r 70' % (FILL, FILL),
          '53 %s %s r 70' % (ALT, ALT),
          '70 _ %s r 70' % FILL, '70 %s %s r 70' % (FILL, FILL),
          '70 %s %s r 70' % (ALT, FILL),
          '70 %s _ r 71' % RIM, '70 %s %s l halt' % (END, END),
          '71 _ %s l 72' % RIM, '71 %s %s l 72' % (FILL, RIM),
          '71 %s %s l 72' % (ALT, RIM),
          '71 %s %s l halt' % (END, END),
          '72 _ _ l 72', '72 %s %s l 72' % (FILL, ALT), '72 %s %s l 72' % (ALT, ALT),
          '72 %s %s l 72' % (RIM, RIM),
          '72 %s %s r 0' % (ANCHOR, ANCHOR),
          '73 _ _ l 72', '73 %s %s l 72' % (FILL, ALT), '73 %s %s l 72' % (ALT, ALT),
          '73 %s %s l 72' % (RIM, RIM), '73 %s %s l halt' % (END, END)]
    R.sort(key=lambda line: FILL in line)
    return '\n'.join(R) + '\n'


def rate(n, seed):
    import random
    rnd = random.Random(seed)
    return [rnd.choice('567888888') for _ in range(n)]


def start_tape(n=260, seed=33):
    cells = {1: RIM}
    for i, sym in enumerate(rate(n, seed)):
        cells[-n - 1 + i] = sym
    cells[-1] = ANCHOR
    cells[-n - 2] = END
    cells[n + 4] = END
    left = ''.join(cells.get(c, '_') for c in range(-n - 2, 0))
    right = ''.join(cells.get(c, '_') for c in range(0, n + 6))
    return left + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('caves.txt', 'w').write(text)
    s = Session(0, None, morphemt=text, init=start_tape()) if False else Session(
        0, None, morphett=text, init=start_tape())
    i = s.advance(4000000)
    print('halted', i['halted'], 'step', i['step'], 'cells', i['ones'],
          'span', i['lo'], i['hi'], 'rules', len(text.splitlines()),
          'symbols', s.symbols, 'rates', len(rate(260, 33)))
    draw(s.snapshot()).save('caves.png')
