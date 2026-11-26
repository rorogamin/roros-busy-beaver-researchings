"""Space-time diagrams for the 37 BB(2,5) Rocq holdouts.

x = tape cell, y = time (downwards).  Each cell is filled with the colour of the
symbol written there; the head is not drawn and there is no grid, so a diagram
shows nothing but symbols.

Palette (index = symbol value, per the project spec):

    0 black, 1 dark gray, 2 gray, 3 light gray, 4 white
"""
import colorsys

from PIL import Image

# Head overlay indices live above every symbol slot, so a symbol can never be
# mistaken for the head.
HEAD_L_IDX = 14
HEAD_R_IDX = 15
HEAD_L = (40, 220, 120)
HEAD_R = (255, 70, 70)

# grey ladder used from 5 symbols up; extra symbols add darker steps below 64.
# Fewer symbols drop interior levels starting from the dark end.
BASE_LADDER = [0, 64, 128, 192, 255]
DROP_ORDER = (64, 192, 128)


def ramp(m):
    """m grey levels from black to white, one per symbol.

    2: 0 255 | 3: 0 128 255 | 4: 0 128 192 255 | 5: 0 64 128 192 255
    6: 0 32 64 128 192 255 | 7: 0 16 32 64 128 192 255 | ...
    """
    m = max(2, int(m))
    if m > 5:
        extra, v = [], 64
        for _ in range(m - 5):
            v //= 2
            extra.append(v)
        return [0] + sorted(extra) + [64, 128, 192, 255]
    levels = list(BASE_LADDER)
    for v in DROP_ORDER[:5 - m]:
        levels.remove(v)
    return levels


# Blaze mode trades palette fidelity for speed: 0 is white, then warm hues.
BLAZE_COLOURS = [
    (255, 255, 255),   # 0 white
    (255, 140, 26),    # 1 orange
    (255, 210, 63),    # 2 yellow
    (255, 95, 162),    # 3 pink
    (57, 208, 216),    # 4 cyan
    (92, 230, 92),     # 5 green
    (160, 108, 255),   # 6 violet
    (255, 80, 80),     # 7 red
    (190, 190, 110),
    (120, 180, 255),
]

# head cells coloured by machine state start here, above every symbol slot
STATE_BASE = 32
TEXT_IDX = 48          # step-number colour in the explore gutter


def state_colour(i, n=2):
    """Rainbow hue for state i, spread by the golden angle."""
    h = (i * 0.618033988749895) % 1.0 if n > 1 else 0.0
    r, g, b = colorsys.hsv_to_rgb(h, 0.72, 1.0)
    return (int(r * 255), int(g * 255), int(b * 255))


def blaze_palette(m):
    pal = [0] * 768
    for i in range(max(1, m)):
        pal[3 * i:3 * i + 3] = list(BLAZE_COLOURS[i % len(BLAZE_COLOURS)])
    pal[3 * HEAD_L_IDX:3 * HEAD_L_IDX + 3] = list(HEAD_L)
    pal[3 * HEAD_R_IDX:3 * HEAD_R_IDX + 3] = list(HEAD_R)
    return pal


def palette(m):
    """768-entry PIL palette for an m-symbol machine, plus head colours."""
    pal = [0] * 768
    for i, v in enumerate(ramp(m)):
        pal[3 * i:3 * i + 3] = [v, v, v]
    pal[3 * HEAD_L_IDX:3 * HEAD_L_IDX + 3] = list(HEAD_L)
    pal[3 * HEAD_R_IDX:3 * HEAD_R_IDX + 3] = list(HEAD_R)
    return pal

MAX_WIDTH = 3000


def parse_std(spec):
    """'1RB---4LB1RA4RA_...' -> trans[state][sym] = (write, dir, next) or None."""
    trans = []
    for block in spec.strip().split('_'):
        if len(block) % 3:
            raise ValueError('ragged block in %r' % spec)
        row = []
        for i in range(0, len(block), 3):
            tok = block[i:i + 3]
            if tok == '---':
                row.append(None)
            else:
                row.append((int(tok[0]), {'L': -1, 'R': 1, 'N': 0}[tok[1].upper()],
                            ord(tok[2]) - ord('A')))
        trans.append(row)
    return trans


MORPHETT_MOVE = {'l': -1, 'r': 1, '*': 0, 'n': 0}


def parse_morphett(text):
    """Morphett 5-tuple format -> (trans, state names, symbols).

        q1 sym write move q2      e.g.  0 _ 1 r 1

    ';' and '#' start comments, 'halt' (or '---') as the next state halts, and
    the start state is the one named "0" (else the first state in the file).
    Symbols are indexed with the blank symbol '_' as 0, so the machine starts on
    a blank tape like every other machine here.  '*' (no move) is direction 0;
    'n' is still read as an alias for old files.
    """
    instrs, states, symbols = [], [], ['_']
    for raw in text.splitlines():
        line = raw.split(';')[0].split('#')[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 5:
            raise ValueError('not a 5-tuple: %r' % raw.strip())
        q, read, write, move, nxt = parts
        d = MORPHETT_MOVE.get(move.lower())
        if d is None:
            raise ValueError('bad move %r in %r' % (move, raw.strip()))
        halt = nxt.lower() in ('halt', 'h', '---')
        if q not in states:
            states.append(q)
        if not halt and nxt not in states:
            states.append(nxt)
        for s in (read, write):
            if s not in symbols:
                symbols.append(s)
        instrs.append((q, read, write, d, None if halt else nxt))
    if not instrs:
        raise ValueError('no instructions')
    if '0' in states:                              # start in state "0" if it exists
        states.remove('0')
        states.insert(0, '0')
    si = {name: i for i, name in enumerate(states)}
    yi = {name: i for i, name in enumerate(symbols)}
    table = {(si[q], yi[r]): (yi[w], d, None if nx is None else si[nx])
             for q, r, w, d, nx in instrs}
    trans = [[table.get((i, j)) for j in range(len(symbols))]
             for i in range(len(states))]
    return trans, states, symbols


def morphett_std(trans, states, symbols):
    """Best-effort standard-format string, '' when it cannot be expressed."""
    if len(symbols) > 10 or len(states) > 26:
        return ''
    letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
    blocks = []
    for row in trans:
        block = ''
        for cell in row:
            if cell is None or cell[2] is None:
                block += '---'               # halting cells look like std format's
            else:
                w, d, nx = cell
                block += '%d%s%s' % (w, 'L' if d < 0 else 'R' if d > 0 else 'N',
                                     letters[nx])
        blocks.append(block)
    return '_'.join(blocks)


def _step(trans, tape, head, state):
    tr = trans[state][tape.get(head, 0)]
    if tr is None:
        return None
    w, d, nxt = tr
    if w:
        tape[head] = w
    else:
        tape.pop(head, None)
    return head + d, nxt


def diagram(spec, steps=200_000, rows=560, margin=2):
    """Render one machine.  Returns (PIL image, info dict)."""
    trans = parse_std(spec)
    m = len(trans[0])

    # pass 1: span of the region that will be visible
    tape, head, state = {}, 0, 0
    lo = hi = 0
    used = 0
    halted = False
    for n in range(steps):
        r = _step(trans, tape, head, state)
        if r is None:
            halted = True
            break
        head, state = r
        lo = min(lo, head)
        hi = max(hi, head)
        used = n + 1
    k = max(1, used // rows) if used else 1
    nrows = max(1, min(rows, (used + k - 1) // k if used else 1))

    # pass 2: replay, snapshotting one row every k steps
    tape, head, state = {}, 0, 0
    snaps = []
    for n in range(used):
        if n % k == 0:
            snaps.append(tuple(tape.items()))
        head, state = _step(trans, tape, head, state)
    if used % k:
        snaps.append(tuple(tape.items()))
    nrows = len(snaps)

    lo -= margin
    hi += margin
    width = hi - lo + 1
    xskip = 1
    if width > MAX_WIDTH:                      # keep the image bounded
        xskip = (width + MAX_WIDTH - 1) // MAX_WIDTH
        width = (width + xskip - 1) // xskip

    px = bytearray(nrows * width)              # 0 == symbol 0 everywhere
    for r, snap in enumerate(snaps):
        base = r * width
        for p, v in snap:
            x = (p - lo) // xskip
            if 0 <= x < width:
                px[base + x] = v if v < m else m - 1
    im = Image.frombytes('P', (width, nrows), bytes(px))
    im.putpalette(palette(m))
    return im.convert('RGB'), {
        'steps': used, 'halted': halted, 'rows': nrows, 'width': width,
        'cells': [lo, hi - 1], 'ones': len(snaps[-1]) if snaps else 0,
    }
