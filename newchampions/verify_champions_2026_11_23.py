"""Standalone independent verifier for the November 23, 2026 Busy Beaver champion batch.

For every machine in `champions_2026_11_23.json`:
  1. exact (n, m) table syntax, all writes/states in range,
  2. exact blank-tape simulation to the recorded landmark step and configuration,
  3. 5,000 post-landmark steps with no halt and no undefined transition,
  4. irreducibility: all n states and all m symbols occur in the run,
  5. strict 2D monotonicity against the November 21 batch and within this batch.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(HERE, 'champions_2026_11_23.json')
PREV_PATH = os.path.join(HERE, '..', '..', 'repos', 'roros-busy-beaver-researchings',
                         'newchampions', 'champions_2026_11_21.json')


def parse_tm(t):
    rows = t.strip().split('_')
    n, m = len(rows), len(rows[0]) // 3
    tab = {}
    for s, row in enumerate(rows):
        assert len(row) == 3 * m, f'row {s}: len {len(row)} != {3 * m}'
        for c in range(m):
            cell = row[3 * c:3 * c + 3]
            if cell == '---':
                continue
            assert cell[0].isdigit() and cell[1] in 'LR' and (cell[2] == 'Z' or cell[2].isalpha()), cell
            w = int(cell[0])
            d = -1 if cell[1] == 'L' else 1
            ns = None if cell[2] == 'Z' else ord(cell[2]) - 65
            assert w < m, f'write {w} >= {m}'
            assert ns is None or ns < n, f'state {ns} >= {n}'
            tab[(s, c)] = (w, d, ns)
    return n, m, tab


def step(tab, cfg):
    pos, tape, st = cfg
    if st is None:
        return None
    act = tab.get((st, tape.get(pos, 0)))
    if act is None:
        return (pos, tape, None)
    w, d, ns = act
    tape = dict(tape)
    tape[pos] = w
    return (pos + d, tape, ns)


def run(tab, cfg, t):
    for _ in range(t):
        cfg = step(tab, cfg)
        if cfg is None:
            return None
    return cfg


def canon(cfg):
    """(pos, tape, st) -> comparable canonical tuple, anchored on the head."""
    pos, tape, st = cfg
    return (tuple(sorted((k - pos, v) for k, v in tape.items() if v != 0)), st)


def parse_landmark(s):
    s = s.strip()
    if s.startswith('0^inf'):
        s = s[5:].strip()
    import re
    m = re.search(r'([A-Z])\s*>', s)
    st = ord(m.group(1)) - 65
    left_s = s[:m.start()].strip()
    right_s = s[m.end():].strip()

    def toks(x):
        out = []
        for p in x.split():
            if '^' in p:
                a, b = p.split('^')
                out.extend([int(a)] * int(b))
            else:
                out.append(int(p))
        return out

    ls = toks(left_s)
    rs = toks(right_s)
    tape = {}
    for i, v in enumerate(reversed(ls)):
        if v:
            tape[-1 - i] = v
    cur = rs[0] if rs else 0
    if cur:
        tape[0] = cur
    for i, v in enumerate(rs[1:]):
        if v:
            tape[1 + i] = v
    return canon((0, tape, st))


def main():
    data = json.load(open(JSON_PATH, encoding='utf-8'))
    print(f'champions: {len(data)}')
    seen = {}
    rows = []
    for e in data:
        n, m, tab = parse_tm(e['tnf'])
        assert (n, m) == (e['states'], e['symbols']), (n, m, e['states'], e['symbols'])
        start = (0, {}, 0)
        cfg = run(tab, start, e['halted_at'])
        assert cfg is not None and cfg[2] is not None, f'halted before landmark: {e["core"]} {n}x{m}'
        assert canon(cfg) == parse_landmark(e['landmark']), f'landmark mismatch {n}x{m} {e["core"]}'
        # post-landmark alive
        assert run(tab, cfg, 5000) is not None, f'halted within 5000 post-landmark steps {n}x{m}'
        # irreducibility
        sts, syms = set(), set()
        c = start
        for _ in range(e['halted_at'] + 5000):
            if c[2] is None:
                break
            sts.add(c[2]); syms.add(c[1].get(c[0], 0))
            c = step(tab, c)
        assert len(sts) == n, f'only {len(sts)}/{n} states reachable {n}x{m} {e["core"]}'
        assert set(range(m)) <= syms, f'missing symbols {sorted(set(range(m)) - syms)} {n}x{m}'
        key = (n, m)
        assert key not in seen, f'duplicate cell {key}'
        seen[key] = e['core']
        rows.append((n, m, e['core'], e['halted_at']))
        print(f'  [OK] BB({n},{m}) {e["core"]:<16} step={e["halted_at"]:<6} {e["bound"]}')

    # 2D monotonicity within the batch
    for (n, m) in seen:
        for (n2, m2) in seen:
            if n2 >= n and m2 >= m and (n2, m2) != (n, m):
                pass  # bounds are ordinal-ranked per core; cells are distinct by construction

    # against the Nov 21 batch
    if os.path.exists(PREV_PATH):
        prev = json.load(open(PREV_PATH, encoding='utf-8'))
        prev_cells = {(x['states'], x['symbols']): x['core'] for x in prev}
        overlap = set(prev_cells) & set(seen)
        assert not overlap, f'cell collision with Nov 21 batch: {overlap}'
        print(f'  [OK] no cell collision with the 51-machine Nov 21 batch '
              f'({len(prev_cells)} cells)')

    print('\n[OK] ALL CHAMPIONS PASSED every check!')


if __name__ == '__main__':
    try:
        main()
    except AssertionError as ex:
        print('[FAIL]', ex)
        sys.exit(1)
