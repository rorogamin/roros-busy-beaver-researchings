"""Structural + dynamical report for machines extracted from championsReal.txt."""
import sys

import analyse
import extract

NSYM_NAME = '0123456789'


def sym_name(j, nsym):
    if nsym <= 10:
        return NSYM_NAME[j]
    return str(j)


def role_table(m):
    tbl, n, k = m['tbl'], m['nstates'], m['nsym']
    roles = analyse.classify(tbl, n)
    lines = []
    for s in range(n):
        cells = []
        for b in range(k):
            v = tbl.get((s, b))
            if v is None:
                cells.append('%s:-' % sym_name(b, k))
            else:
                w, d, nx = v
                cells.append('%s>%s%s%s' % (sym_name(b, k), sym_name(w, k), d,
                                            'H' if nx is None else str(nx)))
        lines.append('  %2d  %-6s %-5s  %s' % (s, roles[s][0], roles[s][1], ' '.join(cells)))
    return roles, lines


def dyn(m, cap):
    tbl = m['tbl']
    # relabel so the start state is 0 (free normalisation)
    tbl, start = analyse.relabel_start(tbl, m['start'])
    res = analyse.run(tbl, start=start, cap=cap)
    return tbl, res


def main():
    ms = extract.extract()
    order = ['BB(6,2)', 'BB(7,2)', 'BB(8,2)', 'BB(9,2)', 'BB(10,2)', 'BB(11,2)',
             'BB(18,2)', 'BB(21,2)', 'BB(40,2)', 'BB(41,2)',
             'BB(19,5)', 'BB(18,7)', 'BB(51,2)', 'BB(56,7)', 'BB(67,2)',
             'BB(4,4)', 'BB(6,4)', 'BB(5,5)', 'BB(6,5)', 'BB(3,6)', 'BB(2,8)']
    caps = {'BB(40,2)': 120000, 'BB(41,2)': 120000, 'BB(51,2)': 120000,
            'BB(56,7)': 120000, 'BB(67,2)': 120000, 'BB(19,5)': 120000,
            'BB(18,7)': 120000}
    for name in order:
        if name not in ms:
            print('== %s: NOT PARSED' % name)
            continue
        m = ms[name]
        print('=' * 78)
        print('%s  %d states, %d symbols, %d defined cells, start %d' % (
            name, m['nstates'], m['nsym'], len(m['tbl']), m['start']))
        roles, lines = role_table(m)
        counts = {}
        for s, r in roles.items():
            counts[r[0]] = counts.get(r[0], 0) + 1
        print('roles:', counts)
        cyc = analyse.cycles(m['tbl'], m['nstates'])
        print('cycles:', ['-'.join(map(str, c)) for c in cyc[:8]])
        if len(lines) <= 21:
            print('\n'.join(lines))
        tbl, res = dyn(m, caps.get(name, 200000))
        hot = max(res['visits'], key=res['visits'].get) if res['visits'] else 0
        tbl2 = tbl
        res2 = analyse.run(tbl2, start=0, cap=caps.get(name, 200000), sample_state=hot, max_samples=5)
        print('run: steps=%d halted=%s ones=%d extent=%d final_state=%d' % (
            res['steps'], res['halted'], res['ones'], res['maxext'], res['state']))
        top = sorted(res['visits'].items(), key=lambda kv: -kv[1])[:6]
        tot = sum(res['visits'].values())
        print('hot states:', ', '.join('%d:%.0f%%' % (s, 100.0 * c / tot) for s, c in top))
        if res['series']:
            pts = [p for p in (25000, 50000, 100000, 200000) if p <= res['steps']]
            print('series (steps, ones, extent):', [(p, dict((s, (o, e)) for s, o, e in res['series']).get(p)) for p in pts])
        print('tape at hot state %d:' % hot)
        for st, r in res2['samples'][:3]:
            runs = len(r)
            mx = max(c for v, c in r)
            print('  %-8d runs=%d maxrun=%d  head: %s ... tail: %s' % (
                st, runs, mx,
                ' '.join('%d^%d' % (v, c) for v, c in r[:8]),
                ' '.join('%d^%d' % (v, c) for v, c in r[-4:])))
        # growth: ones at the end vs a quarter way
        if res['samples']:
            pass
        print()


if __name__ == '__main__':
    main()
