"""A band of weave whose rims crawl out to two fixed walls, then snap back to a
pair of anchors near the middle and grow again: a column of woven triangles."""

PATTERN = ['1', '_']          # write, gap, write, gap ... -- the weave


def machine():
    n = len(PATTERN)
    R = list(range(n)); L = list(range(n, 2 * n))
    lines = []
    for i, q in enumerate(R):                     # rightward passes
        nxt = R[(i + 1) % n]
        for s in ('_', '1'):
            lines.append('%d %s %s r %d' % (q, s, PATTERN[i], nxt))
        lines += ['%d 2 _ r 10' % q,               # met the right rim
                  '%d 8 8 r %d' % (q, q),          # step over the anchors
                  '%d 9 9 r %d' % (q, q)]
    for i, q in enumerate(L):                     # leftward passes
        nxt = L[(i + 1) % n]
        for s in ('_', '1'):
            lines.append('%d %s %s l %d' % (q, s, PATTERN[i], nxt))
        lines += ['%d 3 _ l 20' % q,
                  '%d 8 8 l %d' % (q, q),
                  '%d 9 9 l %d' % (q, q)]
    lines += [
        '10 5 5 l 11',                            # wall -> snap back
    ]
    for sx in ('_', '1', '2', '3', '8', '9'):     # room -> grow one cell
        lines.append('10 %s 2 l 12' % sx)
    for sx in ('_', '1', '2', '3', '8', '9'):
        lines.append('20 %s 3 r 22' % sx)
    lines += [
        '12 _ _ l %d' % L[0],
        '11 _ _ l 11', '11 1 1 l 11', '11 2 2 l 11',
        '11 9 9 r 13',                            # right anchor: stop, back out
        '13 _ 2 l 14', '14 9 9 l %d' % L[0],
        '20 4 4 r 21',
        '22 _ _ r %d' % R[0],
        '21 _ _ r 21', '21 1 1 r 21', '21 3 3 r 21',
        '21 8 8 l 23',
        '23 _ 3 r 24', '24 8 8 r %d' % R[0],
    ]
    return '\n'.join(lines) + '\n'


def start_tape(w):
    fixed = {-w - 1: '4', -3: '3', -2: '8', 2: '9', 3: '2', w + 1: '5'}
    left = ''.join(fixed.get(c, '_') for c in range(-w - 1, 0))
    right = ''.join(fixed.get(c, '_') for c in range(0, w + 2))
    return left + '*' + right


if __name__ == '__main__':
    import sys
    from sim import Session, draw
    w = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 40000
    text = machine()
    s = Session(0, None, morphett=text, init=start_tape(w))
    k = 0
    while True:
        i = s.advance(2000)
        k += 2000
        if i['halted'] or k >= steps:
            break
        print('%6d  span %4d..%4d  ones %4d' % (i['step'], i['lo'], i['hi'], i['ones']))
    print('halted', i['halted'], 'at', i['step'], 'rules', len(text.splitlines()))
    if not i['halted']:
        draw(s.snapshot()).save('_scales_%d.png' % w)
