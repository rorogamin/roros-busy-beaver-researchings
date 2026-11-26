"""Cave carnival: caves open, caves close, every kind in its own colour.

Two stoppers sit inside the band (a near one at first, a far one beyond it) and
an outer rim closes the band.  A rate tape left of the anchor is read once per
pass; each rate letter is a different kind of pass with its own paint tone:

    a  full pass, rim +1                      tone 5
    b  full pass, rim +5                      tone 6
    c  stub to the near stopper               tone 7
    d  stub to the far stopper                tone 9
    e  full pass, rim +5, near stopper +5     tone g
    f  full pass, rim +5, far stopper +5      tone h

A stub paints only out to its stopper, so the band beyond stays dark; a later
full pass sweeps over that dark gap and seals it with a stroke in that pass's
colour.  Caves come out in two different depths, at whatever width the stoppers
and rim happen to have, and each one is ringed by strokes of several colours.
Running out of rate tape halts the machine.

Symbols: '0' anchor, '1' rim, '2' near stopper, '3' far stopper, '4' spent rate
cell, '8' end sentinel, tones '5' '6' '7' '9' 'g' 'h', rates 'a'..'f'.
States: 0 read the rate, 1x walk to the anchor, 2x pass, 3x rim push, 5x stopper
shunt, 40 walk home.
"""

ANCHOR, RIM, NEAR, FAR, SPENT, END = '0', '1', '2', '3', '4', '8'
TONES = ['5', '6', '7', '9', 'g', 'h']
RATES = list('abcdef')
TONE = dict(zip(RATES, TONES))
STOP = {'a': None, 'b': None, 'c': NEAR, 'd': FAR, 'e': None, 'f': None}
RIM_PUSH = {'a': 1, 'b': 5, 'c': 0, 'd': 0, 'e': 5, 'f': 5}
SHUNT = {'e': NEAR, 'f': FAR}
SHUNT_LEN = 5
HOME = '40'
BODY = (RIM, NEAR, FAR)


def chain_rules(R, first, length, who, after):
    """Walk right `length` cells then write `who` and continue in `after`."""
    names = [first] + ['%s%s' % (first, 'abcde'[i]) for i in range(length - 1)]
    for i, name in enumerate(names[:-1]):
        nxt = names[i + 1]
        R.append('%s _ _ r %s' % (name, nxt))
        for t in TONES:
            R.append('%s %s %s r %s' % (name, t, t, nxt))
        for s in BODY:
            R.append('%s %s %s r %s' % (name, s, s, nxt))
    last = names[-1]
    R.append('%s _ %s r %s' % (last, who, after))
    for t in TONES:
        R.append('%s %s %s r %s' % (last, t, who, after))
    for s in BODY:
        R.append('%s %s %s r %s' % (last, s, who, after))
    return names


def machine():
    R = ['0 %s %s l 0' % (SPENT, SPENT),
         '0 %s %s l 0' % (ANCHOR, ANCHOR),
         '0 _ _ l 0',
         '0 %s %s l halt' % (END, END)]
    for t in TONES:
        R.append('0 %s %s l 0' % (t, t))
    for s in BODY:
        R.append('0 %s %s l 0' % (s, s))
    for sym in RATES:
        R.append('0 %s %s r 1%s' % (sym, SPENT, sym))
        R += ['1%s %s %s r 1%s' % (sym, SPENT, SPENT, sym),
              '1%s %s %s r 2%s' % (sym, ANCHOR, ANCHOR, sym)]
    for sym in RATES:
        tone, p = TONE[sym], '2' + sym
        R.append('%s _ %s r %s' % (p, tone, p))
        for t in TONES:
            R.append('%s %s %s r %s' % (p, t, tone, p))
        for s in (NEAR, FAR):
            if STOP[sym] == s:
                R.append('%s %s %s l %s' % (p, s, s, HOME))
            elif SHUNT.get(sym) == s:
                R.append('%s %s _ r 5%s' % (p, s, sym))
            else:
                R.append('%s %s %s r %s' % (p, s, s, p))
        if STOP[sym] is None:
            R.append('%s %s _ r 3%s' % (p, RIM, sym))
            R.append('%s %s %s l %s' % (p, RIM, RIM, HOME))
        else:
            R.append('%s %s %s l %s' % (p, RIM, RIM, HOME))
        R.append('%s %s %s l halt' % (p, END, END))
    # rim pushes: walk right k cells, drop the rim, go home
    for sym in RATES:
        k = RIM_PUSH[sym]
        if k:
            chain_rules(R, '3' + sym, k, RIM, HOME)
    # stopper shunts: drop the stopper k cells further out, then keep sweeping
    for sym, who in SHUNT.items():
        chain_rules(R, '5' + sym, SHUNT_LEN, who, '2' + sym)
    # walk home doing nothing at all
    R.append('%s %s %s l %s' % (HOME, ANCHOR, ANCHOR, '0'))
    R.append('%s _ _ l %s' % (HOME, HOME))
    for t in TONES:
        R.append('%s %s %s l %s' % (HOME, t, t, HOME))
    for s in BODY:
        R.append('%s %s %s l %s' % (HOME, s, s, HOME))
    R.sort(key=lambda line: '9' in line)
    return '\n'.join(R) + '\n'


def rate(n, seed):
    import random
    rnd = random.Random(seed)
    return [rnd.choice('ccddab' + 'ef' + 'c' * 6) for _ in range(n)]


def start_tape(n=70, seed=5, near=30, far=70, rim=110):
    cells = {}
    for i, sym in enumerate(rate(n, seed)):
        cells[-n - 1 + i] = sym
    cells[-1] = ANCHOR
    cells[-n - 2] = END
    cells[near] = NEAR
    cells[far] = FAR
    cells[rim] = RIM
    cells[rim + 150] = END
    left = ''.join(cells.get(c, '_') for c in range(-n - 2, 0))
    right = ''.join(cells.get(c, '_') for c in range(0, rim + 152))
    return left + '*' + right


if __name__ == '__main__':
    from sim import Session, draw
    text = machine()
    open('carnival.txt', 'w').write(text)
    s = Session(0, None, morphett=text, init=start_tape())
    i = s.advance(4000000)
    print('halted', i['halted'], 'step', i['step'], 'cells', i['ones'],
          'span', i['lo'], i['hi'], 'rules', len(text.splitlines()),
          'symbols', s.symbols)
    draw(s.snapshot()).save('carnival.png')
