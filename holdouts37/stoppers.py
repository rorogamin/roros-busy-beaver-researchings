"""Two-rim caves: an outer rim and an inner stopper, both creeping right at
their own chaotic rates, five cells at a time.

A rate tape left of the anchor is read once per pass:

    '5'  full pass   -- sweep to the outer rim, push it out five cells
    '7'  stub pass   -- sweep only to the stopper, then turn back
    '8'  full pass   -- as '5', and shunt the stopper five cells right as well

Because a stub stops on the stopper, it bites the *current* gap out of the band
rather than a fixed distance, and full passes cap those bites.  The rim and the
stopper advance on independent irregular rate symbols, so the gap -- the cave
width -- wanders, and the caves arrive one after another in every size.  Runs
out of rate tape -> halt.

Symbols: '0' anchor, '1' outer rim, '6' stopper, '3' end of tape, '4' spent rate
cell, '5'/'7'/'8' rates, '9' tone out, '2' tone home.
States: 0 read the rate, 10/11/12 walk back to the anchor, 20 full pass,
21 stub pass, 22 full pass + stopper shunt, 24 shunt chain, 30 rim-push chain,
40 walk home repainting.
"""

ANCHOR, RIM, STOPPER, END, SPENT = '0', '1', '6', '3', '4'
OUT, HOME = '9', '2'
FULL, STUB, SHUNT = '5', '7', '8'
PUSH = 5


def machine():
    R = ['0 %s %s l 0' % (SPENT, SPENT),
         '0 %s %s l 0' % (ANCHOR, ANCHOR),
         '0 %s %s l 0' % (OUT, OUT),
         '0 %s %s l 0' % (HOME, HOME),
         '0 _ _ l 0',
         '0 %s %s l halt' % (END, END),
         '0 %s %s r 10' % (FULL, SPENT),
         '0 %s %s r 11' % (STUB, SPENT),
         '0 %s %s r 12' % (SHUNT, SPENT)]
    for walk, start in (('10', '20'), ('11', '21'), ('12', '22')):
        R += ['%s %s %s r %s' % (walk, SPENT, SPENT, walk),
              '%s %s %s r %s' % (walk, ANCHOR, ANCHOR, start)]
    # full pass: paint out, step over the stopper, reach the rim
    R += ['20 _ %s r 20' % OUT, '20 %s %s r 20' % (OUT, OUT),
          '20 %s %s r 20' % (HOME, OUT), '20 %s %s r 20' % (STOPPER, STOPPER),
          '20 %s _ r 30' % RIM, '20 %s %s l halt' % (END, END)]
    # stub pass: paint out, turn on the stopper
    R += ['21 _ %s r 21' % OUT, '21 %s %s r 21' % (OUT, OUT),
          '21 %s %s r 21' % (HOME, OUT), '21 %s %s l 40' % (STOPPER, STOPPER),
          '21 %s %s l 40' % (RIM, RIM), '21 %s %s l halt' % (END, END)]
    # full pass that also shunts the stopper
    R += ['22 _ %s r 22' % OUT, '22 %s %s r 22' % (OUT, OUT),
          '22 %s %s r 22' % (HOME, OUT), '22 %s _ r 24' % STOPPER,
          '22 %s _ r 30' % RIM, '22 %s %s l halt' % (END, END)]
    # shove the stopper PUSH cells right, then carry on with the pass
    chain = ['24']
    for k in range(PUSH):
        chain.append('24' + 'abcdefgh'[k])
    for a, b in zip(chain, chain[1:]):
        R += ['%s _ _ r %s' % (a, b)]
        if b != chain[-1]:
            R += ['%s %s %s r 22' % (a, s, STOPPER) for s in (OUT, HOME)]
    R += ['%s _ %s r 22' % (chain[-1], STOPPER),
          '%s %s %s r 22' % (chain[-1], OUT, STOPPER),
          '%s %s %s r 22' % (chain[-1], HOME, STOPPER),
          '%s %s %s l 40' % (chain[-1], RIM, RIM),
          '%s %s %s l halt' % (chain[-1], END, END)]
    # push the outer rim PUSH cells right
    chain = ['30']
    for k in range(PUSH):
        chain.append('30' + 'abcdefgh'[k])
    for a, b in zip(chain, chain[1:]):
        R += ['%s _ _ r %s' % (a, b)]
        if b != chain[-1]:
            R += ['%s %s %s r 22' % (a, s, RIM) for s in (OUT, HOME)]
    R += ['%s _ %s l 40' % (chain[-1], RIM),
          '%s %s %s l 40' % (chain[-1], OUT, RIM),
          '%s %s %s l 40' % (chain[-1], HOME, RIM),
          '%s %s %s l halt' % (chain[-1], END, END)]
    # walk home repainting in the other tone
    R += ['40 %s %s l 40' % (OUT, HOME), '40 %s %s l 40' % (HOME, HOME),
          '40 %s %s l 40' % (STOPPER, STOPPER), '40 %s %s l 40' % (RIM, RIM),
          '40 _ _ l 40', '40 %s %s r 0' % (ANCHOR, ANCHOR)]
    R.sort(key=lambda line: OUT in line)
    return '\n'.join(R) + '\n'


def rate(n, seed):
    import random
    rnd = random.Random(seed)
    return [rnd.choice('7777775555888') for _ in range(n)]


def start_tape(n=70, seed=41, stopper=30, rim=38):
    cells = {}
    for i, sym in enumerate(rate(n, seed)):
        cells[-n - 1 + i] = sym
    cells[-1] = ANCHOR
    cells[-n - 2] = END
    cells[rim] = RIM
    cells[stopper] = STOPPER
    cells[rim + 260] = END
    left = ''.join(cells.get(c, '_') for c in range(-n - 2, 0))
    right = ''.join(cells.get(c, '_') for c in range(0, rim + 262))
    return left + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('stoppers.txt', 'w').write(text)
    s = Session(0, None, morphett=text, init=start_tape())
    i = s.advance(4000000)
    counts = {}
    for sym in rate(70, 41):
        counts[sym] = counts.get(sym, 0) + 1
    print('halted', i['halted'], 'step', i['step'], 'cells', i['ones'],
          'span', i['lo'], i['hi'], 'rules', len(text.splitlines()),
          'symbols', s.symbols, 'rates', counts)
    draw(s.snapshot()).save('stoppers.png')
