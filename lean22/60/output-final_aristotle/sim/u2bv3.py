"""A first look at the shape of the `P3` row with a `V` after an absorbing `U(2,8)`
(`ANALYSIS.md` §36, second row) — the row that is still open.

`passes` prints the computation cut into maximal monotone runs of the head: for each run
the state and position at its two ends, the number of steps, and the tape word before and
after over the cells the run touches.  This is the picture from which a stage
decomposition (and then a Lean proof) is read off.

Exploratory only; nothing here is machine-checked.
"""

import sys
from u21b import T
from u2bv2 import word, out, steps


def passes(t, mp, verbose=True):
    l = list(word(t, mp))
    q, k = 'B', 3
    n = steps(t, mp)
    i = 0
    total = 0
    while i < n:
        q0, k0 = q, k
        before = list(l)
        lo = hi = k
        d0 = None
        cnt = 0
        while i < n:
            w, d, s = T[(q, l[k])]
            # stop the run when the direction changes
            if d0 is not None and d != d0:
                break
            d0 = d
            l[k] = w
            k += d
            q = s
            lo, hi = min(lo, k), max(hi, k)
            i += 1
            cnt += 1
        total += cnt
        if verbose:
            print('%s%-4d -> %s%-4d  %4d steps  cells [%d,%d]' % (q0, k0, q, k, cnt, lo, hi))
            print('   in : %s' % ''.join(map(str, before[lo:hi + 1])))
            print('   out: %s' % ''.join(map(str, l[lo:hi + 1])))
    print('total %d steps, end %s%d, %s' % (total, q, k,
          'word ok' if l == out(t, mp) else 'WORD MISMATCH'))


def profile(t, mp, prom=4):
    """The big turning points of the head: local extrema of prominence >= `prom`."""
    l = list(word(t, mp))
    q, k = 'B', 3
    pos = [(0, q, k)]
    for i in range(steps(t, mp)):
        w, d, s = T[(q, l[k])]
        l[k] = w
        k += d
        q = s
        pos.append((i + 1, q, k))
    # keep only the turning points whose next extremum is at least `prom` away
    out_ = [pos[0]]
    last = pos[0]
    for j in range(1, len(pos) - 1):
        a, b, c = pos[j - 1][2], pos[j][2], pos[j + 1][2]
        if (b - a) * (c - b) < 0:  # local extremum
            if abs(b - last[2]) >= prom:
                out_.append(pos[j])
                last = pos[j]
    out_.append(pos[-1])
    prev = None
    for (i, q0, k0) in out_:
        print('step %5d  %s%-4d %s' % (i, q0, k0,
              '' if prev is None else '(%+d cells, %d steps)' % (k0 - prev[2], i - prev[0])))
        prev = (i, q0, k0)


def cut(t, mp, b=28):
    """Cut the computation at the crossings of the boundary between cells `b-1` and `b`
    (by default the left end of the run of `u`s), and print each segment."""
    l = list(word(t, mp))
    q, k = 'B', 3
    n = steps(t, mp)
    i = 0
    seg = 0
    while i < n:
        side = k >= b
        q0, k0, i0 = q, k, i
        before = list(l)
        lo = hi = k
        while i < n and (k >= b) == side:
            w, d, s = T[(q, l[k])]
            l[k] = w
            k += d
            q = s
            lo, hi = min(lo, k), max(hi, k)
            i += 1
        seg += 1
        print('[%d] %s%-4d -> %s%-4d  %4d steps (%d..%d)  cells [%d,%d]'
              % (seg, q0, k0, q, k, i - i0, i0, i, lo, hi))
        print('    in : %s' % ''.join(map(str, before[lo:hi + 1])))
        print('    out: %s' % ''.join(map(str, l[lo:hi + 1])))
    print('end %s%d, %s' % (q, k, 'word ok' if l == out(t, mp) else 'WORD MISMATCH'))


if __name__ == '__main__':
    t = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    mp = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    mode = sys.argv[3] if len(sys.argv) > 3 else 'profile'
    if mode == 'cut':
        cut(t, mp)
    elif mode == 'passes':
        passes(t, mp)
    else:
        profile(t, mp)
