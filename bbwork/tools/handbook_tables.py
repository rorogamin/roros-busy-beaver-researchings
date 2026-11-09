"""Generate the data appendices of FGH_HANDBOOK.md from championsReal.txt.

Everything here is measured, not quoted: the transition tables are parsed from the
ledger's 5-tuple strings, the dynamics come from running those tables, and the tape
shapes are run-length encodings of the actual tape.

Usage:  python handbook_tables.py > handbook_appendix.md
"""
import sys

import analyse
import extract

ORDER = ['BB(6,2)', 'BB(7,2)', 'BB(8,2)', 'BB(9,2)', 'BB(10,2)', 'BB(11,2)',
         'BB(18,2)', 'BB(21,2)', 'BB(40,2)', 'BB(41,2)',
         'BB(19,5)', 'BB(18,7)', 'BB(51,2)', 'BB(56,7)', 'BB(67,2)',
         'BB(4,4)', 'BB(6,4)', 'BB(5,5)', 'BB(6,5)', 'BB(3,6)', 'BB(2,8)']

CAP = 400000


def sym(j, k):
    return '0123456789'[j] if k <= 10 else str(j)


def cell(tbl, s, b, k):
    v = tbl.get((s, b))
    if v is None:
        return '---'
    w, d, n = v
    return '%s%s%s' % (sym(w, k), d, 'H' if n is None else n)


def measure(name, m):
    tbl, start = analyse.relabel_start(m['tbl'], m['start'])
    res = analyse.run(tbl, start=start, cap=CAP)
    tot = sum(res['visits'].values()) or 1
    top = sorted(res['visits'].items(), key=lambda kv: -kv[1])[:3]
    hot = top[0][0] if top else 0
    runs = analyse.rle(res['tape'])
    longest = max((c for v, c in runs), default=0)
    return dict(tbl=tbl, start=start, res=res, top=top, tot=tot, runs=runs,
                longest=longest)


def main():
    ms = extract.extract()
    data = {}
    for name in ORDER:
        if name in ms:
            data[name] = measure(name, ms[name])

    print('## Appendix A - measured profiles\n')
    print('All figures from a run of %d steps on a blank tape, start state normalised'
          % CAP)
    print('to 0. "hot" is the share of all steps spent in the two most visited states;')
    print('"runs" and "max" describe the tape at the end of the window (run-length')
    print('encoding: runs = number of maximal constant blocks, max = longest block).\n')
    print('| machine | st | sy | roles (w/s/b) | hot states | ones | extent | runs | max block |')
    print('|---|---|---|---|---|---|---|---|---|')
    for name in ORDER:
        if name not in data:
            continue
        d = data[name]
        m = ms[name]
        res = d['res']
        roles = analyse.classify(m['tbl'], m['nstates'])
        cnt = {'write': 0, 'sweep': 0, 'branch': 0}
        for r in roles.values():
            cnt[r[0]] += 1
        hot = ', '.join('%d:%.0f%%' % (s, 100.0 * c / d['tot']) for s, c in d['top'][:2])
        print('| %s | %d | %d | %d/%d/%d | %s | %d | %d | %d | %d |' % (
            name, m['nstates'], m['nsym'], cnt['write'], cnt['sweep'], cnt['branch'],
            hot, res['ones'], res['maxext'], len(d['runs']), d['longest']))

    print('\n### Tape shapes at the end of the window\n')
    print('The first 14 runs, then the last 4 (`v^n` = n consecutive cells holding v).\n')
    for name in ORDER:
        if name not in data:
            continue
        r = data[name]['runs']
        head = ' '.join('%d^%d' % (v, c) for v, c in r[:14])
        tail = ' '.join('%d^%d' % (v, c) for v, c in r[-4:])
        print('- **%s** (%d runs): `%s ... %s`' % (name, len(r), head, tail))

    print('\n## Appendix B - full transition tables\n')
    print('Generated from the 5-tuple strings in `championsReal.txt`. A cell `---`')
    print('means no transition (the machine halts if it ever reads it). `H` is an')
    print('explicit halt row. Rows with all cells defined are complete machines.\n')
    for name in ORDER:
        if name not in data:
            continue
        d = data[name]
        m = ms[name]
        n, k = m['nstates'], m['nsym']
        roles = analyse.classify(m['tbl'], n)
        if n > 21:
            print('### %s (%d states, %d symbols)\n' % (name, n, k))
            print('Too wide to print here; see `championsReal.txt`. Role census: %s.\n'
                  % ', '.join('%s %d' % (r, sum(1 for x in roles.values() if x[0] == r))
                              for r in ('write', 'sweep', 'branch')))
            continue
        print('### %s (%d states, %d symbols, start %d)\n'
              % (name, n, k, m['start']))
        hdr = ' | '.join('read %s' % sym(b, k) for b in range(k))
        print('| state | role | %s |' % hdr)
        print('|---' * (k + 2) + '|')
        for s in range(n):
            cells = ' | '.join('`%s`' % cell(d['tbl'], s, b, k) for b in range(k))
            print('| %d | %s %s | %s |' % (s, roles[s][0], roles[s][1], cells))
        print()


if __name__ == '__main__':
    main()
