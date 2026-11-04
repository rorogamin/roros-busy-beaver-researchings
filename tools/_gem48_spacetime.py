"""Space-time diagrams for the gem48 machine over 1,000,000 blank-tape steps.

Machine: gem48_morphett.txt (== rocq/gemini_epsilon1_tm_48s_v2_fix.v, verified).

Outputs:
  gem48_spacetime_1m.png           tape state at window ends, 1 row per 1000
                                   steps (top = step 0, bottom = step 1,000,000)
  gem48_spacetime_1m_activity.png  write-activity heat: red = mostly 1-writes,
                                   blue = mostly 0-writes, magenta = both,
                                   white = untouched; 1 row per 1000 steps
  gem48_spacetime_boot1641.png     full resolution: one row PER STEP for the
                                   first 1641 steps (boot -> step-1641 seed)

Caption strip under each image: magenta bars at cells -17 / -14 (the
step-1641 worm counter block), green bar at cell 0 (start head).

Run: py -3.14 tools/_gem48_spacetime.py
"""
import math

import numpy as np
from PIL import Image, ImageDraw, ImageFont

# ---------------------------------------------------------------- table
def parse_morphett(path):
    tab, seen = {}, set()
    for raw in open(path, encoding='utf-8'):
        line = raw.split(';')[0].strip()
        if not line:
            continue
        q, rd, wr, d, nq = line.split()
        sym = 1 if rd == '1' else 0
        out = 1 if wr == '1' else 0
        nx = 'Halt' if nq.lower().startswith('halt') else nq
        assert (q, sym) not in seen
        seen.add((q, sym))
        tab[(q, sym)] = (out, d.upper(), nx)
    return tab

MT = parse_morphett('gem48_morphett.txt')

# ---------------------------------------------------------------- simulate
N, WIN, ZOOM = 1_000_000, 1000, 1641

ones = set()
state, head = '0', 0
snaps = [set()]                  # state snapshot at each window end (incl. t=0)
wins1, wins0 = [{}], [{}]         # per-window write counters, keyed by cell
zaft = [set()]                   # zoom: state after each step (0..ZOOM)
zwrites = []                     # zoom: (cell, bit) written on steps 1..ZOOM
step_writes = []                 # all (cell, bit) writes over the full run
hi = lo = 0
zhi = zlo = 0
haltstep = None
for step in range(1, N + 1):
    bit = 1 if head in ones else 0
    wbit, d, nx = MT[(state, bit)]
    if wbit:
        ones.add(head)
    else:
        ones.discard(head)
    cell = head
    head += 1 if d == 'R' else -1
    if wbit:
        wins1[-1][cell] = wins1[-1].get(cell, 0) + 1
        zwrites.append((cell, 1))
    else:
        wins0[-1][cell] = wins0[-1].get(cell, 0) + 1
        zwrites.append((cell, 0))
    step_writes.append((cell, wbit))
    hi = max(hi, head); lo = min(lo, head)
    if step <= ZOOM:
        zhi = max(zhi, head); zlo = min(zlo, head)
        zaft.append(set(ones))
    if step % WIN == 0 or step == N:
        snaps.append(set(ones))
        wins1.append({}); wins0.append({})
    state = 'Halt' if nx == 'Halt' else nx
    if nx == 'Halt':
        haltstep = step
        break

left_cells = len(ones)
print(f'run done: halt={haltstep} head-extremes [{lo},{hi}] no-halt-cells={left_cells}')
V = hi - lo + 1
ZV = zhi - zlo + 1

# window rows used (the sim may rotate one empty final dict)
nrows = len(snaps)                              # includes the t=0 row

# ---------------------------------------------------------------- images
def colmap(span_lo, span_hi, maxw=1400):
    """cell -> column index (may compress if span too wide)."""
    nspan = span_hi - span_lo + 1
    if nspan <= maxw:
        return lambda c: c - span_lo
    s = (maxw - 1) / (nspan - 1)
    return lambda c: int(round((c - span_lo) * s))

WHITE = np.uint8(247)
MK = np.array([255, 0, 200], np.uint8)          # magenta landmark
GR = np.array([0, 170, 0], np.uint8)            # green landmark (cell 0)

def caption_bar(barw, colf, texts, height=26):
    bar = np.full((height, barw, 3), 255, np.uint8)
    im = Image.fromarray(bar); d = ImageDraw.Draw(im)
    for txt, cell, rgb in texts:
        x = colf(cell)
        d.rectangle([x - 1, 0, x, height], fill=rgb)
        d.text((x + 3, 5), txt, fill=(60, 60, 60))
    d.text((4, 5), 'x-axis: tape cells (left .. right of head range)',
           fill=(120, 120, 120))
    return np.asarray(im)

font = ImageFont.load_default()

# ------------- 1. overview state image
colf = colmap(lo, hi)
arr = np.full((nrows, max(V, colf(hi) + 1), 3), 247, np.uint8)
for ri, s in enumerate(snaps):
    for c in s:
        arr[ri, colf(c)] = 25
data_w = colf(hi) + 1
# 100k separators (every 100 rows), only over white cells
for r in range(100, nrows, 100):
    m = (arr[r, :, 0] == 247) & (arr[r, :, 1] == 247) & (arr[r, :, 2] == 247)
    arr[r, m] = 200
cap = caption_bar(data_w, colf, [('-17', -17, (255, 0, 200)),
                                 ('-14', -14, (255, 0, 200)),
                                 ('0', 0, (0, 170, 0))])
arr = np.vstack([arr, cap])
Image.fromarray(arr).save('gem48_spacetime_1m.png', optimize=True)
print('wrote gem48_spacetime_1m.png', arr.shape)

# ------------- 2. overview activity image
HS = nrows - 1
rows = np.full((HS, data_w, 3), 255, np.uint8)
cols1 = []; cols0 = []
for dw1, dw0 in list(zip(wins1, wins0))[:HS]:
    a1 = np.zeros(data_w, np.int32); a0 = np.zeros(data_w, np.int32)
    for c, n in dw1.items(): a1[colf(c)] += n
    for c, n in dw0.items(): a0[colf(c)] += n
    cols1.append(a1); cols0.append(a0)
for i, (a1, a0) in enumerate(zip(cols1, cols0)):
    tot = a1 + a0
    m = tot > 0
    ratio = np.zeros(data_w, np.float32)
    ratio[m] = np.abs(a1[m] - a0[m]) / tot[m]
    inten = np.zeros(data_w, np.float32)
    inten[m] = np.minimum(1.0, 0.45 + 0.11 * np.log2(tot[m]))
    g = 255 * (1 - 2 * ratio)
    ch1 = 255 * (2 * a1 >= tot); chb = 255 * (a0 >= a1)
    rgb = np.zeros((data_w, 3), np.float32)
    rgb[:, 0] = ch1 * inten; rgb[:, 2] = chb * inten
    rgb[:, 1] = np.maximum(0, g * inten)
    rows[i, m] = rgb[m].astype(np.uint8)
# 100k separators
for r in range(100, HS, 100):
    rows[r] = (rows[r].astype(np.int32) * 4 // 5).astype(np.uint8)
cap2 = caption_bar(data_w, colf, [('-17', -17, (255, 0, 200)),
                                  ('-14', -14, (255, 0, 200)),
                                  ('0', 0, (0, 170, 0))])
rows = np.vstack([rows, cap2])
Image.fromarray(rows).save('gem48_spacetime_1m_activity.png', optimize=True)
print('wrote gem48_spacetime_1m_activity.png', rows.shape)

# ------------- 3. zoom: first 1641 steps, full resolution state
colz = colmap(zlo, zhi, maxw=1400)
W = zhi - zlo + 1
zarr = np.full((len(zaft), W, 3), 247, np.uint8)
for ri, s in enumerate(zaft):
    for c in s:
        zarr[ri, colz(c)] = 25
imgw2 = W
def capzoom(colf, texts, height=26):
    bar = np.full((height, colz(zhi) + 1, 3), 255, np.uint8)
    im = Image.fromarray(bar); d = ImageDraw.Draw(im)
    for txt, cell, rgb in texts:
        x = colf(cell)
        d.rectangle([x - 1, 0, x, height], fill=rgb)
        d.text((x + 3, 5), txt, fill=(60, 60, 60))
    return np.asarray(im)
capz = capzoom(colz, [('-17', -17, (255, 0, 200)), ('-14', -14, (255, 0, 200)),
                      ('0', 0, (0, 170, 0))])
zarr = np.vstack([zarr, capz])
Image.fromarray(zarr).save('gem48_spacetime_boot1641.png', optimize=True)
print('wrote gem48_spacetime_boot1641.png', zarr.shape)

# ------------- 4. bonus: first-1641 activity, one row per step
rowsA = np.full((ZOOM, W, 3), 255, np.uint8)
for i, (c, b) in enumerate(zwrites[:ZOOM]):
    rowsA[i, colz(c)] = (255, 40, 40) if b else (40, 40, 255)
for r in range(50, ZOOM, 50):
    rowsA[r] = (rowsA[r].astype(np.int32) * 4 // 5).astype(np.uint8)
rowsA = np.vstack([rowsA, capz])
Image.fromarray(rowsA).save('gem48_spacetime_boot1641_activity.png', optimize=True)
print('wrote gem48_spacetime_boot1641_activity.png', rowsA.shape)
