"""Exact Python mirror of BB/TM.lean semantics (list-based, canonical blank tails)."""
import re


def parse_tnf(t):
    rows = t.strip().split('_')
    n = len(rows)
    m = len(rows[0]) // 3
    tm = {}
    for s, row in enumerate(rows):
        assert len(row) == 3 * m, (s, len(row), 3 * m)
        for c in range(m):
            cell = row[3 * c:3 * c + 3]
            if cell == '---':
                continue
            w = int(cell[0])
            d = cell[1]
            assert d in 'LR'
            nx = None if cell[2] == 'Z' else ord(cell[2]) - 65
            tm[(s, c)] = (w, d, nx)
    return n, m, tm


def cons0(w, xs):
    return [] if (w == 0 and not xs) else [w] + xs


def step(tm, cfg):
    st, left, cur, right = cfg
    if st is None:
        return None
    act = tm.get((st, cur))
    if act is None:
        return (None, left, cur, right)
    w, d, nx = act
    if d == 'L':
        if not left:
            return (nx, [], 0, cons0(w, right))
        return (nx, left[1:], left[0], cons0(w, right))
    if not right:
        return (nx, cons0(w, left), 0, [])
    return (nx, cons0(w, left), right[0], right[1:])


def run(tm, cfg, t):
    for _ in range(t):
        cfg = step(tm, cfg)
        if cfg is None:
            return None
    return cfg


INIT = (0, [], 0, [])


def parse_landmark(s):
    """`0^inf 3^1 2^2 A> 1^4 4 2` -> (st, left, cur, right)."""
    s = s.strip()
    if s.startswith('0^inf'):
        s = s[5:].strip()
    mstate = re.search(r'([A-Z])\s*>', s)
    st = ord(mstate.group(1)) - 65
    left_s = s[:mstate.start()].strip()
    right_s = s[mstate.end():].strip()

    def toks(x):
        out = []
        for p in x.split():
            p = p.replace('(', '').replace(')', '').replace('{', '').replace('}', '')
            if 'inf' in p:
                continue
            if '^' in p:
                a, b = p.split('^')
                out.extend([int(a)] * int(b))
            elif p.isdigit():
                out.append(int(p))
        return out

    ls = toks(left_s)
    rs = toks(right_s)
    cur = rs[0] if rs else 0
    right = rs[1:] if rs else []
    left = list(reversed(ls))
    return (st, left, cur, right)


def landmark_match(cfg, spec):
    """Tool landmarks are patterns: left exact, right is a minimum-length prefix."""
    st, left, cur, right = cfg
    pst, pleft, pcur, pright = parse_landmark(spec)
    if (st, left, cur) != (pst, pleft, pcur):
        return False
    return right[:len(pright)] == pright


def landmark_clean(cfg, spec):
    """True when nothing but blanks follows the matched landmark prefix."""
    st, left, cur, right = cfg
    pst, pleft, pcur, pright = parse_landmark(spec)
    if (st, left, cur) != (pst, pleft, pcur):
        return False
    return all(x == 0 for x in right[len(pright):])


def fmt_landmark(cfg):
    st, left, cur, right = cfg
    def seg(xs):
        if not xs:
            return ''
        out, i = [], 0
        while i < len(xs):
            j = i
            while j + 1 < len(xs) and xs[j + 1] == xs[i]:
                j += 1
            out.append(f'{xs[i]}^{j - i + 1}' if j > i else str(xs[i]))
            i = j + 1
        return ' '.join(out)
    l = seg(list(reversed(left)))
    r = seg([cur] + right)
    return ('0^inf ' + (l + ' ' if l else '') + chr(65 + st) + '> ' + r).strip()


def all_states_used(tm, n, m, cfg, steps):
    seen = set()
    syms = set()
    c = cfg
    for _ in range(steps):
        st, left, cur, right = c
        if st is None:
            break
        seen.add(st)
        syms.add(cur)
        c = step(tm, c)
        if c is None:
            break
        seen.update([x for x in [c[0]] if x is not None])
    return len(seen) == n, sorted(syms)


def chunk_configs(tm, K, chunk=35):
    """Configs after each chunk boundary, as Lean will compute them."""
    out = []
    cfg = INIT
    remaining = K
    while remaining > 0:
        t = min(chunk, remaining)
        cfg = run(tm, cfg, t)
        if cfg is None:
            raise RuntimeError('halted before boundary')
        out.append((t, cfg))
        remaining -= t
    return out
