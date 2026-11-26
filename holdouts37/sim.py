"""Interactive simulation sessions for the holdout viewer.

A Session keeps the live machine (tape, head, state, step) plus a growing
space-time picture: one stored row every k steps, with k doubling whenever the
row list gets long, so the picture stays bounded for arbitrarily many steps.

Three pictures come out of a snapshot:

  default  exactly 512 x 768, symbols only (head trail optional, green L / red R)
  explore  a wide, tall, scrollable picture: symbols unchanged, the head cell
           coloured by machine state (rainbow) and step numbers down the left
  blaze    512 x 768 at low internal resolution for speed, warm palette with
           white = 0, orange = 1, yellow/pink/... above
"""
import io
from array import array

from PIL import Image, ImageDraw

from render import (HEAD_L_IDX, HEAD_R_IDX, STATE_BASE, TEXT_IDX, blaze_palette,
                    morphett_std, palette, parse_morphett, parse_std, state_colour)

LETTERS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'

SIZE = (512, 768)
FAST = (256, 384)            # blaze renders here, then scales up to SIZE
MAX_ROWS = 420
MAX_CELLS = 1_500_000        # cap on stored cells; dense tapes thin the history

EXPLORE_CELL = 2             # pixels per tape cell
EXPLORE_STEP = 4             # pixels per sampled step
EXPLORE_GUTTER = 58          # step-number column
EXPLORE_ROWS = 360           # newest rows kept for the scrollable view
EXPLORE_COLS = 3000          # widest tape column count before cells merge


def _merge(rows):
    """Halve the row count, folding each pair's writes into the later row."""
    out = []
    for i in range(0, len(rows) - 1, 2):
        a, b = rows[i], rows[i + 1]
        out.append((a[0] + b[0], b[1], b[2], b[3]))
    if len(rows) % 2:
        out.append(rows[-1])
    return out


class Session:
    def __init__(self, mid, spec=None, tape='bi', morphett=None, init=None):
        self.mid = mid
        if morphett is not None:
            self.trans, self.states, self.symbols = parse_morphett(morphett)
            self.morphett = morphett.strip()
            self.spec = morphett_std(self.trans, self.states, self.symbols)
        else:
            self.trans = parse_std(spec)
            self.states = list(LETTERS[:len(self.trans)])
            self.symbols = [str(i) for i in range(len(self.trans[0]))]
            self.morphett = ''
            self.spec = spec
        # 'bi' = cells both ways; 'semi' = cells >= 0 only, wall left of cell 0
        self.semi = (tape == 'semi')
        self.parse_init(init)
        self.reset()

    def symbol_index(self, ch):
        if ch in ('_', '.'):
            return 0
        if ch in self.symbols:
            return self.symbols.index(ch)
        raise ValueError('%r is not a symbol of this machine (it uses %s)'
                         % (ch, ' '.join(self.symbols)))

    def parse_init(self, init):
        """Starting tape from a string with * marking the head.

        The head sits on the first cell to the right of the *, cells before it
        fill the tape to the left; '1*01' means cell -1 is 1 and the head is on
        cell 0 holding 0.  A semi-infinite tape has no cells left of the wall,
        so there the text simply starts at cell 0 and the head moves along it.
        Blank can be written '0', '_' or '.'.
        """
        text = ''.join(ch for ch in (init or '') if not ch.isspace())
        if text.count('*') > 1:
            raise ValueError('use a single * to mark the head')
        if '*' in text:
            left, _, right = text.partition('*')
        else:                       # no marker: the tape starts under the head
            left, right = '', text
        cells = {}
        if self.semi:
            head = len(left)
            for i, ch in enumerate(left + right):
                v = self.symbol_index(ch)
                if v:
                    cells[i] = v
            lo, hi = 0, len(left) + len(right) - 1
        else:
            head = 0
            for i, ch in enumerate(left):
                v = self.symbol_index(ch)
                if v:
                    cells[i - len(left)] = v
            for j, ch in enumerate(right):
                v = self.symbol_index(ch)
                if v:
                    cells[j] = v
            lo, hi = -len(left), len(right) - 1
        if not text:
            lo = hi = 0
        self.initial = cells
        self.head0 = head
        self.init_lo = min(lo, head)
        self.init_hi = max(hi, head)

    def table(self):
        """Instruction rows for display: one token per (state, symbol)."""
        rows = []
        for i, row in enumerate(self.trans):
            cells = []
            for cell in row:
                if cell is None or cell[2] is None:
                    cells.append('---')          # halts: same notation as std format
                else:
                    w, d, nx = cell
                    cells.append('%s%s%s' % (
                        self.symbols[w], 'L' if d < 0 else 'R' if d > 0 else 'N',
                        self.states[nx]))
            rows.append(cells)
        return rows

    def reset(self):
        self.tape = dict(self.initial)
        self.head = self.head0
        self.state = 0
        self.dir = 0
        self.step = 0
        self.k = 1
        first = array('i')                    # the starting tape in row 0
        for p in sorted(self.initial):
            first.append(p)
            first.append(self.initial[p])
        self.rows = [(first, self.head, 0, 0)]   # (writes since previous row, head, dir, state)
        self.pending = []
        self.row_cells = 0
        self.lo = self.init_lo
        self.hi = self.init_hi
        self.halted = False

    def advance(self, n):
        trans, tape = self.trans, self.tape
        head, state, step, k, d0 = self.head, self.state, self.step, self.k, self.dir
        lo, hi, rows = self.lo, self.hi, self.rows
        semi, halted = self.semi, self.halted
        row_cells = self.row_cells
        pending = self.pending
        if halted:
            return self.info()
        for _ in range(max(0, n)):
            tr = trans[state][tape.get(head, 0)]
            if tr is None:               # undefined transition: stops as it is
                halted = True
                break
            w, d, nxt = tr
            if w:
                if tape.get(head) != w:
                    pending.append(head)
                    pending.append(w)
                tape[head] = w
            elif head in tape:
                pending.append(head)
                pending.append(0)
                del tape[head]
            head += d
            if semi and head < 0:        # wall: a left move from cell 0 stays put
                head = 0
            step += 1
            d0 = d
            if head < lo:
                lo = head
            elif head > hi:
                hi = head
            if step % k == 0:
                rows.append((array('i', pending), head, d0, state))
                row_cells += len(pending) // 2
                pending = []
                if len(rows) > MAX_ROWS:      # fold pairs, keep k aligned
                    rows = _merge(rows)
                    k *= 2
                while row_cells > MAX_CELLS and len(rows) > 1:
                    row_cells -= len(rows[0][0]) // 2   # drop the oldest history
                    rows.pop(0)
            if nxt is None:              # Morphett 'halt': this step still happens
                halted = True
                break
            state = nxt
        self.head, self.state, self.step, self.dir = head, state, step, d0
        self.halted = halted
        self.row_cells = row_cells
        self.pending = pending
        self.lo, self.hi, self.k, self.rows = lo, hi, k, rows
        return self.info()

    def snapshot(self):
        return {'step': self.step, 'lo': self.lo, 'hi': self.hi,
                'm': len(self.trans[0]), 'states': len(self.trans),
                'rows': list(self.rows), 'k': self.k}

    def info(self, radius=64):
        h = self.head
        cells = [self.tape.get(p, 0) for p in range(h - radius, h + radius + 1)]
        return {
            'id': self.mid,
            'spec': self.spec,
            'morphett': self.morphett,
            'table': {'states': self.states, 'symbols': self.symbols,
                      'rows': self.table()},
            'step': self.step,
            'head': self.head,
            'state': self.states[self.state] if self.state < len(self.states)
                     else '?',
            'ones': len(self.tape),
            'lo': self.lo,
            'hi': self.hi,
            'halted': self.halted,
            'rows': len(self.rows),
            'k': self.k,
            'tapeMode': 'semi' if self.semi else 'bi',
            'tape': cells,
            'tapeHead': radius,
        }


def draw(snap, mode='default', head=False):
    """Render a snapshot in one of the three visualisation modes."""
    if mode == 'explore':
        return explore(snap)
    fast = mode == 'blaze'
    max_w, max_h = FAST if fast else SIZE

    lo, hi = snap['lo'] - 2, snap['hi'] + 2
    width = hi - lo + 1
    xskip = max(1, (width + max_w - 1) // max_w)
    w = (width + xskip - 1) // xskip
    rows = snap['rows']
    rskip = max(1, (len(rows) + max_h - 1) // max_h)
    nrows = (len(rows) + rskip - 1) // rskip
    m = max(2, snap['m'])
    px = bytearray(w * nrows)
    cols = bytearray(w)                  # tape as columns, carried forward
    base = 0
    for i, (deltas, h, d, st) in enumerate(rows):
        for j in range(0, len(deltas), 2):
            x = (deltas[j] - lo) // xskip
            if 0 <= x < w:
                v = deltas[j + 1]
                cols[x] = v if v < m else m - 1
        if i % rskip:
            continue
        px[base:base + w] = cols
        if head:
            x = (h - lo) // xskip
            if 0 <= x < w:
                px[base + x] = (HEAD_L_IDX if d < 0 else
                                HEAD_R_IDX if d > 0 else 0)
        base += w
    im = Image.frombytes('P', (w, nrows), bytes(px))
    im.putpalette(blaze_palette(m) if fast else palette(m))
    return im.convert('RGB').resize(SIZE, Image.NEAREST)


def explore(snap):
    """Scrollable view: symbols keep their colours, the head is state-coloured,
    step numbers run down the left gutter."""
    allrows = snap['rows']
    start = max(0, len(allrows) - EXPLORE_ROWS)
    rows = allrows[start:]
    lo = snap['lo'] - 1
    hi = snap['hi'] + 1
    m = max(2, snap['m'])
    nst = max(1, snap.get('states', 2))
    span = hi - lo + 1
    ctp = max(1, -(-span // EXPLORE_COLS))       # tape cells per screen column
    ncols = -(-span // ctp)
    W = EXPLORE_GUTTER + ncols * EXPLORE_CELL
    H = max(1, len(rows)) * EXPLORE_STEP

    slots = min(nst, 16)        # palette room for state hues
    pal = palette(m)
    for s in range(slots):
        pal[3 * (STATE_BASE + s):3 * (STATE_BASE + s) + 3] = list(state_colour(s, nst))
    pal[3 * TEXT_IDX:3 * TEXT_IDX + 3] = [150, 156, 166]

    px = bytearray(W * H)
    k = snap['k']
    last = snap['step']
    cols = bytearray(ncols)
    exp = [bytes([v]) * EXPLORE_CELL for v in range(256)]

    def apply(deltas):
        for j in range(0, len(deltas), 2):
            x = (deltas[j] - lo) // ctp
            if 0 <= x < ncols:
                v = deltas[j + 1]
                cols[x] = v if v < m else m - 1

    for deltas, h, d, st in allrows[:start]:       # history before the window
        apply(deltas)
    for y, (items, h, d, st) in enumerate(rows):
        apply(items)
        buf = bytearray(EXPLORE_GUTTER) + b''.join(exp[v] for v in cols)
        x = EXPLORE_GUTTER + ((h - lo) // ctp) * EXPLORE_CELL
        if 0 <= x < W:
            wide = max(EXPLORE_CELL, 4)          # a touch wider than a cell, to be visible
            buf[x:x + wide] = bytes([STATE_BASE + (st % slots)]) * wide
        base = y * EXPLORE_STEP * W
        for dy in range(EXPLORE_STEP):
            off = base + dy * W
            px[off:off + W] = buf

    im = Image.frombytes('P', (W, H), bytes(px))
    im.putpalette(pal)
    d = ImageDraw.Draw(im)
    for y in range(0, len(rows), 20):
        step = last - (len(rows) - 1 - y) * k
        d.text((3, y * EXPLORE_STEP + 1), format(step, ','), fill=TEXT_IDX)
    return im


def encode(im):
    buf = io.BytesIO()
    im.save(buf, 'PNG', optimize=True)
    return buf.getvalue()
