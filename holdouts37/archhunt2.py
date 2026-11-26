"""Generate lots of arch-machine mutants, score how textured their diagrams are,
and show the most interesting ones in one sheet."""
import random
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


def score(im):
    g = im.convert('L')
    w, h = g.size
    px = g.load()
    tex = 0
    runs = 0
    for y in range(h):
        prev = px[0, y]
        n = 0
        for x in range(1, w):
            v = px[x, y]
            if v != prev:
                n += 1
                prev = v
        runs += n
        if n >= 6:
            tex += 1
    return tex + runs / 2000.0


def main(out='sheet3.png', tries=200, keep=16, steps=300000, seed=11):
    rnd = random.Random(seed)
    base = parse(BASE)
    keys = list(base)
    scored = []
    for n in range(tries):
        m = dict(base)
        for _ in range(rnd.choice((1, 2, 2, 3))):
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
        text = emit(m)
        s = Session(0, None, morphett=text, init='*_2')
        i = s.advance(steps)
        if i['halted'] or i['ones'] < 300 or (i['hi'] - i['lo']) > steps:
            continue
        im = draw(s.snapshot())
        scored.append((score(im), n, im, text))
    scored.sort(reverse=True)
    best = scored[:keep]
    cols, tw, th = 4, 128, 192
    rows = (len(best) + cols - 1) // cols
    sheet = Image.new('RGB', (cols * tw, rows * (th + 14)), (25, 28, 33))
    d = ImageDraw.Draw(sheet)
    for idx, (sc, n, im, _) in enumerate(best):
        x, y = (idx % cols) * tw, (idx // cols) * (th + 14)
        sheet.paste(im.resize((tw, th)), (x, y + 14))
        d.text((x + 4, y + 2), '#%d %.0f' % (n, sc), fill=(200, 205, 215))
    sheet.save(out)
    with open(out + '.txt', 'w') as fh:
        for sc, n, _, text in best:
            fh.write('### %d score %.0f\n%s\n' % (n, sc, text))
    print('%d candidates scored, %d shown -> %s' % (len(scored), len(best), out))


if __name__ == '__main__':
    main()
