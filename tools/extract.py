"""Extract machine specs from championsReal.txt and parse them."""
import os
import re

import analyse

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'championsReal.txt')

INLINE = re.compile(r'[0-9A-Za-z_-]*_[0-9A-Za-z_-]+')
TABULAR = re.compile(r'^\s*\d+\s+[_01]\s+[_01]\s+[lrLR]\s+(\d+|halt)\s*$')


def read_lines():
    return open(SRC, encoding='utf-8').read().split('\n')


def block_after(lines):
    """Lines of the first M = ( ... ) block, if any."""
    out = []
    depth = 0
    started = False
    for line in lines:
        if not started:
            if 'M = (' in line:
                started = True
                depth = 1
            continue
        depth += line.count('(') - line.count(')')
        out.append(line)
        if depth <= 0:
            break
    return out


def extract():
    lines = read_lines()
    heads = []
    for i, line in enumerate(lines):
        m = re.match(r'^BB\((\d+)(?:,(\d+))?\)', line)
        if m:
            heads.append((i, int(m.group(1)), int(m.group(2)) if m.group(2) else 2))
    machines = {}
    for h, (start_i, n, k) in enumerate(heads):
        end_i = heads[h + 1][0] if h + 1 < len(heads) else len(lines)
        entry = lines[start_i:end_i]
        name = 'BB(%d,%d)' % (n, k)
        if name in machines:
            continue
        text = '\n'.join(entry)

        spec = None
        for tok in re.split(r'[,\s]+', text):
            if INLINE.fullmatch(tok) and len(tok) > 15:
                try:
                    tbl, ns, nsym, start = analyse.parse_inline(tok)
                except Exception:
                    continue
                if ns == n:
                    spec = tok
                    break
        if spec:
            tbl, ns, nsym, start = analyse.parse_inline(spec)
            machines[name] = dict(tbl=tbl, nstates=ns, nsym=nsym, start=start, spec=spec)
            continue

        rows = [l for l in entry if TABULAR.match(l)]
        if len(rows) >= n:
            tbl, _, _, start = analyse.parse_tabular(rows)
            machines[name] = dict(tbl=tbl, nstates=n, nsym=2, start=start,
                                  spec='tabular, %d rows' % len(rows))
            continue

        blk = block_after(entry)
        if blk:
            first = next((l for l in blk if '(' in l), None)
            if first is not None:
                cells = len(re.findall(r'\((-?\d+)\s*,\s*-?\d+\s*,\s*(\d+|halt|hr)\)', first))
                nsym = max(2, cells)
                st = re.search(r'start from state (\d+)', text)
                start = int(st.group(1)) if st else 0
                tbl, ns, _, _ = analyse.parse_tuple_dict(blk, nsym=nsym, start=0)
                machines[name] = dict(tbl=tbl, nstates=ns, nsym=nsym, start=start,
                                      spec='tuple block, %d symbols' % nsym)
    return machines


if __name__ == '__main__':
    ms = extract()
    def key(s):
        a = re.findall(r'\d+', s)
        return (int(a[0]), int(a[1]))
    for name in sorted(ms, key=key):
        m = ms[name]
        tbl = m['tbl']
        states = sorted({s for (s, _) in tbl})
        halts = sum(1 for s in states for b in range(m['nsym']) if (s, b) not in tbl)
        print('%-10s nsym=%d states=%3d cells=%4d start=%2d halts=%2d  %s' % (
            name, m['nsym'], len(states), len(tbl), m['start'], halts, m['spec'][:40]))
