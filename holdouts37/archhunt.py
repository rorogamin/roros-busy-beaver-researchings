"""Design-by-perturbation: mutate an arch machine, keep the ones that still run
long, and tile their space-time diagrams into one contact sheet to look at."""
import random
import sys

from PIL import Image, ImageDraw

from sim import Session, draw

BASE = """0 _ 1 r 0
0 1 _ l 0
0 2 2 l 1
1 1 1 l 1
1 _ 1 r 2
2 1 1 r 2
2 2 2 r 2
2 _ _ r 3
3 _ 1 l 3
3 1 _ r 3
3 2 2 r 4
4 1 1 r 4
4 _ 1 l 5
5 2 2 l 5
5 1 1 l 5
5 _ _ r 0
"""


def parse(text):
    m = {}
    for line in text.strip().splitlines():
        q, r, w, d, n = line.split()
        m[(q, r)] = (w, d, n)
    return m


def emit(m):
    return '\n'.join('%s %s %s %s %s' % (q, r, w, d, n)
                     for (q, r), (w, d, n) in m.items()) + '\n'


def render(text, steps, init='*_2'):
    s = Session(0, None, morphett=text, init=init)
    i = s.advance(steps)
    if i['halted'] or i['ones'] < 200:
        return None
    return draw(s.snapshot())


def main(seed_text, out, count=24, steps=300000, seed=1):
    rnd = random.Random(seed)
    base = parse(seed_text)
    keys = list(base)
    tiles = []
    for n in range(count):
        m = dict(base)
        for _ in range(rnd.choice((1, 1, 2, 3))):
            k = rnd.choice(keys)
            w, d, nx = m[k]
            what = rnd.choice(('w', 'd', 'n'))
            if what == 'w':
                w = rnd.choice(('_', '1', '2'))
            elif what == 'd':
                d = 'r' if d == 'l' else 'l'
            else:
                nx = rnd.choice(sorted({v[2] for v in base.values()}))
            m[k] = (w, d, nx)
        im = render(emit(m), steps)
        if im is None:
            continue
        tiles.append((n, im, emit(m)))
    cols, tw, th = 4, 128, 192
    rows = (len(tiles) + cols - 1) // cols
    sheet = Image.new('RGB', (cols * tw, rows * (th + 14)), (25, 28, 33))
    d = ImageDraw.Draw(sheet)
    for idx, (n, im, _) in enumerate(tiles):
        x, y = (idx % cols) * tw, (idx // cols) * (th + 14)
        sheet.paste(im.resize((tw, th)), (x, y + 14))
        d.text((x + 4, y + 2), '#%d' % n, fill=(200, 205, 215))
    sheet.save(out)
    with open(out + '.txt', 'w') as fh:
        for n, _, text in tiles:
            fh.write('### %d\n%s\n' % (n, text))
    print('%d of %d machines kept -> %s' % (len(tiles), count, out))


if __name__ == '__main__':
    main(BASE, sys.argv[1] if len(sys.argv) > 1 else 'sheet.png',
         int(sys.argv[2]) if len(sys.argv) > 2 else 24)
