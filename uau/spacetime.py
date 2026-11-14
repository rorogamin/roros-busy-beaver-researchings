"""Space-time diagrams for uubin.tm.

x = tape cell, y = time (downwards).  Light = blank, dark = 1, red = head.
The tape is raw bits, so a block of k ones is a dark column of height k and a
group shows up as the thin 1 in its marker field.

  spacetime.png        the three panels side by side
  spacetime_boot.png   panel A alone: the bootstrap and the first append
  spacetime_halt.png   panel B alone: the halt_on=2 run, start to halt
  spacetime_long.png   panel C alone: the shipped machine, 120k steps
"""
from PIL import Image, ImageDraw

import uubin as U

BLANK = (255, 255, 255)
ONE = (32, 48, 100)
HEAD = (220, 40, 40)
GRID = (228, 228, 234)
INK = (70, 70, 80)


def trace(tm, start, steps, blank=True):
    tape = {} if blank else dict(enumerate(U.start_tape()))
    pos, st = 0, start
    writes, heads = [], []
    n = 0
    for n in range(steps):
        b = tape.get(pos, 0)
        if (st, b) not in tm.tr:
            break
        w, mv, nx = tm.tr[(st, b)]
        writes.append((n, pos, w))
        tape[pos] = w
        pos += 1 if mv == 'R' else -1
        heads.append(pos)
        st = nx
    return writes, heads, n


def panel(tm, start, steps, rows, xscale=1, grid=5, yscale=1):
    """Return (image, lo, hi, steps_done) for one run."""
    writes, heads, n = trace(tm, start, steps)
    lo = min([p for _, p, _ in writes] + heads + [0]) - 2
    hi = max([p for _, p, _ in writes] + heads + [0]) + 2
    width = hi - lo + 1
    spr = max(1, (n + 1) // rows)
    px = bytearray(width * rows)
    cur = bytearray(width)
    for i, (_, p, w) in enumerate(writes):
        cur[p - lo] = 1 if w else 0
        r = i // spr
        if r >= rows:
            break
        base = r * width
        for x, v in enumerate(cur):
            if v:
                px[base + x] = 1
    for i, h in enumerate(heads):
        r = i // spr
        if r >= rows:
            break
        px[r * width + (h - lo)] = 2
    im = Image.frombytes('P', (width, rows), bytes(px))
    pal = [0, 0, 0] * 256
    for idx, col in ((0, BLANK), (1, ONE), (2, HEAD)):
        pal[3 * idx:3 * idx + 3] = list(col)
    im.putpalette(bytes(pal))
    im = im.convert('RGB')
    if grid:
        d = ImageDraw.Draw(im)
        for x in range(0, width, grid):
            d.line([(x, 0), (x, rows)], fill=GRID)
        # redraw the tape and head on top of the gridlines
        for y in range(rows):
            for x in range(width):
                idx = px[y * width + x]
                if idx:
                    im.putpixel((x, y), ONE if idx == 1 else HEAD)
    if xscale != 1 or yscale != 1:
        im = im.resize((width * xscale, rows * yscale), Image.NEAREST)
    return im, lo, hi, n


def label(im, text, xy, fill=INK):
    ImageDraw.Draw(im).text(xy, text, fill=fill)


def composite():
    tm2, s2 = U.build(2)
    tm5, s5 = U.build(5)
    a = panel(tm2, s2, 300, 300, xscale=4, grid=5, yscale=4)    # bootstrap
    b = panel(tm2, s2, 7000, 1400, xscale=3, grid=5)            # to the halt
    c = panel(tm5, s5, 120000, 1200, xscale=1, grid=0)          # steady state
    for name, args in (('spacetime_boot.png', a), ('spacetime_halt.png', b),
                       ('spacetime_long.png', c)):
        args[0].save(name)
    pad, top, bottom = 24, 22, 40
    W = sum(im.width for im, _, _, _ in (a, b, c)) + pad * 4
    H = max(im.height for im, _, _, _ in (a, b, c)) + top + bottom
    out = Image.new('RGB', (W, H), (250, 250, 252))
    x = pad
    titles = (('A  blank tape', '  %d steps' % a[3]),
              ('B  halt-on-2', '   %d steps, halts' % b[3]),
              ('C  shipped', '   %d steps, no halt' % c[3]))
    for (im, lo, hi, n), title in zip((a, b, c), titles):
        out.paste(im, (x, top))
        for k, line in enumerate(title):
            label(out, line, (x, 3 + 9 * k))
        label(out, 'time', (x, top + im.height + 3))
        ppc = im.width / (hi - lo + 1)
        step = 10 if hi - lo <= 40 else 20
        for cell in range(lo - lo % step + step, hi, step):
            label(out, str(cell), (int(x + (cell - lo) * ppc), top + im.height + 13))
        label(out, 'cell ->', (x, top + im.height + 24))
        x += im.width + pad
    out.save('spacetime.png')
    print('spacetime.png', out.size)


if __name__ == '__main__':
    composite()
