"""Sample random *total* Turing machines (every rule defined, so they never halt)
and look at what their space-time diagrams do."""
import random
import sys

from PIL import Image, ImageDraw

from sim import Session, draw

SONE = ('_', '1', '2')


def sample(rnd, states=6, syms=3, sweep_bias=0.85):
    rules = {}
    for q in range(states):
        pref = rnd.choice('lr')
        for s in range(syms):
            w = rnd.choice(('_', '1', '2'))
            d = pref if rnd.random() < sweep_bias else ('r' if pref == 'l' else 'l')
            n = str(rnd.randrange(states))
            rules['%d %s' % (q, SONE[s])] = '%s %s %s' % (w, d, n)
    return rules


def text_of(rules):
    return '\n'.join('%s %s' % (k, v) for k, v in rules.items()) + '\n'


def main(out='randsheet.png', tries=120, steps=1000000, seed=3):
    rnd = random.Random(seed)
    tiles = []
    for n in range(tries):
        text = text_of(sample(rnd))
        s = Session(0, None, morphett=text, init='*_2')
        i = s.advance(steps)
        if i['halted'] or i['ones'] < 50 or i['hi'] - i['lo'] > 200000:
            continue
        tiles.append((n, draw(s.snapshot()), text, i))
    cols, tw, th = 8, 128, 192
    rows = (len(tiles) + cols - 1) // cols
    sheet = Image.new('RGB', (cols * tw, rows * (th + 14)), (25, 28, 33))
    d = ImageDraw.Draw(sheet)
    for idx, (n, im, _, _) in enumerate(tiles):
        x, y = (idx % cols) * tw, (idx // cols) * (th + 14)
        sheet.paste(im.resize((tw, th)), (x, y + 14))
        d.text((x + 4, y + 2), '#%d' % n, fill=(200, 205, 215))
    sheet.save(out)
    with open(out + '.txt', 'w') as fh:
        for n, _, text, i in tiles:
            fh.write('### %d span %d..%d ones %d\n%s\n' % (n, i['lo'], i['hi'], i['ones'], text))
    print('%d of %d kept -> %s' % (len(tiles), tries, out))


if __name__ == '__main__':
    main(*sys.argv[1:2], **({'tries': int(sys.argv[2])} if len(sys.argv) > 2 else {}))
