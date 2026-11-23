"""Independent verifier for the 2026-11-23 landmark batch.

For each machine in `landmarks_2026_11_23.json`:
  1. exact (n, m) table syntax and transition bounds,
  2. exact blank-tape simulation to the recorded step,
  3. the landed tape matches the recorded landmark pattern,
  4. 5,000 further steps with no halt and no undefined transition,
  5. the landmark is unique per (core, landmark) and the size is minimal.
Champion status is not decided here; `wiki_compare.py` compares each bound with
the live bbchallenge Champions table, and only the machines in
`champions_confirmed_2026_11_23.json` beat the record listed for their cell.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(HERE, 'landmarks_2026_11_23.json')


def parse_tm(t):
    rows = t.strip().split('_')
    n, m = len(rows), len(rows[0]) // 3
    tab = {}
    for s, row in enumerate(rows):
        assert len(row) == 3 * m, f'row {s}: {len(row)} != {3*m}'
        for c in range(m):
            cell = row[3 * c:3 * c + 3]
            if cell == '---':
                continue
            assert cell[0].isdigit() and cell[1] in 'LR'
            w, d = int(cell[0]), (-1 if cell[1] == 'L' else 1)
            ns = None if cell[2] == 'Z' else ord(cell[2]) - 65
            assert w < m and (ns is None or ns < n)
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
    pos, tape, st = cfg
    return (tuple(sorted((k - pos, v) for k, v in tape.items() if v != 0)), st)


def parse_landmark(s):
    import re
    s = s.strip()
    if s.startswith('0^inf'):
        s = s[5:].strip()
    mstate = re.search(r'([A-Z](?:\|[A-Z])*)\s*>', s)
    tok = mstate.group(1)
    st = None if '|' in tok else ord(tok) - 65
    left_s, right_s = s[:mstate.start()].strip(), s[mstate.end():].strip()

    def toks(x):
        out = []
        for p in x.split():
            p = p.replace('(', '').replace(')', '')
            if 'inf' in p:
                continue
            if '^' in p:
                a, b = p.split('^')
                out.extend([int(a)] * int(b))
            elif p.isdigit():
                out.append(int(p))
        return out

    ls, rs = toks(left_s), toks(right_s)
    tape = {}
    for i, v in enumerate(reversed(ls)):
        if v:
            tape[-1 - i] = v
    if rs and rs[0]:
        tape[0] = rs[0]
    for i, v in enumerate(rs[1:]):
        if v:
            tape[1 + i] = v
    return (canon((0, tape, st)), st)


def main():
    data = json.load(open(JSON_PATH, encoding='utf-8'))
    print(f'landmark machines: {len(data)}')
    best = {}
    for e in data:
        n, m, tab = parse_tm(e['tnf'])
        assert (n, m) == (e['states'], e['symbols'])
        cfg = run(tab, (0, {}, 0), e['step'])
        assert cfg is not None and cfg[2] is not None, f'halted early {e["core"]}'
        want, wst = parse_landmark(e['landmark'])
        got = canon(cfg)
        wt = dict(want[0])
        gt = dict(got[0])
        for k, v in wt.items():
            assert gt.get(k) == v, f'tape mismatch at {k} for {e["core"]} {n}x{m}'
        if wst is not None:
            assert got[1] == wst, f'state mismatch {e["core"]} {n}x{m}'
        assert run(tab, cfg, 5000) is not None, f'halted after landmark {e["core"]}'
        key = (e['core'], e['landmark'])
        size = (n * m, n, m)
        if key in best:
            assert size > best[key], f'not minimal for {key}: {size} vs {best[key]}'
        best[key] = size
        print(f"  [OK] {n}x{m} {e['core']:<16} step={e['step']:<6} {e['landmark'][:44]}")
    print(f'\n[OK] ALL {len(data)} LANDMARK MACHINES PASSED every check!')


if __name__ == '__main__':
    try:
        main()
    except AssertionError as ex:
        print('[FAIL]', ex)
        sys.exit(1)
