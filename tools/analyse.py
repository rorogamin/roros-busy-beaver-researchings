"""Parse and structurally analyse the machines listed in championsReal.txt.

Formats handled:
  A  inline 2-symbol:  "1RB1RA_1RC1RZ_..."      (cells of 3 chars, 2 per state)
  B  inline k-symbol:  "1RB3LB4LC2RA4LB_..."    (cells of 3 chars, k per state)
  C  tabular 2-symbol: rows "state _/1 l/r next"
  D  tuple dict:       "s: ((w, d, n), (w, d, n))"   d in {-1,1}
  E  tuple list:       "((w, d, n), (w, d, n))"      implicit state order
"""
import re
import sys


def sym(ch):
    return 0 if ch in '-_' else int(ch)


def parse_inline(spec):
    blocks = [b for b in spec.split('_') if b]
    k = len(blocks[0]) // 3
    tbl = {}
    for st, b in enumerate(blocks):
        for j in range(k):
            cell = b[3 * j:3 * j + 3]
            if cell[0] in '-_':
                continue
            w, d, ns = cell[0], cell[1], cell[2]
            nxt = None if ns in 'Zz' else ord(ns.upper()) - ord('A')
            tbl[(st, j)] = (int(w), d.upper(), nxt)
    return tbl, len(blocks), k, 0


def parse_tabular(lines):
    tbl = {}
    start = 0
    for line in lines:
        m = re.match(r'^\s*(\d+)\s+([_01])\s+([_01])\s+([lrLR])\s+(\d+|halt)\s*$', line)
        if not m:
            continue
        st = int(m.group(1))
        rd = sym(m.group(2))
        wr = sym(m.group(3))
        d = 'R' if m.group(4).lower() == 'r' else 'L'
        nx = None if m.group(5) == 'halt' else int(m.group(5))
        tbl[(st, rd)] = (wr, d, nx)
    return tbl, None, 2, start


def parse_tuple_dict(lines, nsym=2, start=0):
    """lines like '   3: ((1, -1, 10), (1, -1, 4)),'  or without the label."""
    tbl = {}
    order = 0
    for line in lines:
        m = re.match(r'^\s*(\d+)?\s*:\s*\((.*)\)\s*,?\s*$', line)
        if m:
            st = int(m.group(1)) if m.group(1) else order
            order = st + 1
            body = m.group(2)
            cells = re.findall(r'\((\d+|-?\d*)\s*,\s*(-?\d+)\s*,\s*(\d+|halt|hr)\)', body)
            for j, (w, d, nx) in enumerate(cells[:nsym]):
                nxt = None if nx in ('halt', 'hr') else int(nx)
                tbl[(st, j)] = (int(w), 'R' if int(d) > 0 else 'L', nxt)
        else:
            if line.strip().startswith('(('):
                cells = re.findall(r'\((\d+)\s*,\s*(-?\d+)\s*,\s*(\d+|halt|hr)\)', line)
                st = order
                order += 1
                for j, (w, d, nx) in enumerate(cells[:nsym]):
                    nxt = None if nx in ('halt', 'hr') else int(nx)
                    tbl[(st, j)] = (int(w), 'R' if int(d) > 0 else 'L', nxt)
    return tbl, order, nsym, start


def relabel_start(tbl, start):
    """Permute state names so the start state becomes 0 (free normalisation)."""
    if start == 0:
        return tbl, 0
    states = sorted({s for (s, _) in tbl})
    mapping = {start: 0}
    nxt = 1
    for s in states:
        if s not in mapping:
            mapping[s] = nxt
            nxt += 1
    out = {}
    for (s, b), (w, d, n) in tbl.items():
        out[(mapping.get(s, s), b)] = (w, d, None if n is None else mapping.get(n, n))
    return out, 0


# ---------------------------------------------------------------- structure

def classify(tbl, nstates):
    """Role signature per state: pure sweep / pure writer / mixed / halt."""
    roles = {}
    for s in range(nstates):
        cells = [(b, v) for (st, b), v in tbl.items() if st == s]
        if not cells:
            roles[s] = ('halt', '-', 0)
            continue
        dirs = {v[1] for (_, v) in cells}
        ws = {v[0] for (b, v) in cells}
        reads = {b for (b, _) in cells}
        if ws == reads and len(dirs) == 1:
            roles[s] = ('sweep', dirs.pop(), len(cells))
        elif len(dirs) == 1 and ws != reads:
            roles[s] = ('write', dirs.pop(), len(cells))
        else:
            roles[s] = ('branch', '/'.join(sorted(dirs)), len(cells))
    return roles


def cycles(tbl, nstates, limit=200000):
    """Short cycles in the state graph (state sequences), as a structural cue."""
    adj = {s: set() for s in range(nstates)}
    for (s, b), (w, d, n) in tbl.items():
        if n is not None:
            adj[s].add(n)
    found = []
    for s in range(nstates):
        # BFS shortest path from each successor back to s
        for t in adj[s]:
            if t == s:
                found.append([s])
                continue
            prev = {t: None}
            queue = [t]
            while queue and len(prev) < 400:
                u = queue.pop(0)
                for v in adj[u]:
                    if v == s:
                        path = [u]
                        while prev[path[-1]] is not None:
                            path.append(prev[path[-1]])
                        found.append([s] + list(reversed(path)))
                        queue = []
                        break
                    if v not in prev:
                        prev[v] = u
                        queue.append(v)
                else:
                    continue
                break
    uniq = []
    for c in found:
        key = tuple(sorted(c))
        if key not in [tuple(sorted(u)) for u in uniq]:
            uniq.append(c)
    return uniq[:12]


def rle(tape):
    if not tape:
        return []
    lo, hi = min(tape), max(tape)
    out = []
    cur = tape.get(lo, 0)
    cnt = 0
    for p in range(lo, hi + 1):
        v = tape.get(p, 0)
        if v == cur:
            cnt += 1
        else:
            out.append((cur, cnt))
            cur, cnt = v, 1
    out.append((cur, cnt))
    return out


def run(tbl, start=0, cap=200000, sample_state=None, max_samples=8):
    series = []
    tape, head, state = {}, 0, start
    steps = 0
    maxext = 0
    ones_series = []
    rle_samples = []
    visits = {}
    next_sample = 0
    while steps < cap:
        tr = tbl.get((state, tape.get(head, 0)))
        if tr is None:
            return dict(halted=True, steps=steps, tape=tape, head=head, state=state,
                        ones=sum(1 for v in tape.values() if v), maxext=maxext,
                        visits=visits, samples=rle_samples, series=series)
        visits[state] = visits.get(state, 0) + 1
        w, d, n = tr
        if (state == sample_state and steps > 0 and tape
                and len(rle_samples) < max_samples and steps >= next_sample):
            rle_samples.append((steps, rle(tape)))
            next_sample = steps + max(1, cap // (max_samples + 1))
        tape[head] = w
        head += 1 if d == 'R' else -1
        state = n
        steps += 1
        if steps % 1000 == 0:
            if tape:
                maxext = max(maxext, max(tape) - min(tape) + 1)
            series.append((steps, sum(1 for v in tape.values() if v), max(tape) - min(tape) + 1 if tape else 0))
    return dict(halted=False, steps=steps, tape=tape, head=head, state=state,
                ones=sum(1 for v in tape.values() if v), maxext=maxext,
                visits=visits, samples=rle_samples, series=series)
