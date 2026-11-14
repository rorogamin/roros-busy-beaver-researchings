"""Measure the reachable/bisimulation state count of the BVE composed table.

The 46-state table is entered at state 0 on the first zero of the H/E
separator.  This script does not change the table: it computes
  * the states reachable from 0 under both symbols, and
  * the Moore partition of the reachable table, with a missing row treated
    as the shared halt arm.
It prints the raw and minimised counts and writes no files.

Run: python tools/bve_minimise.py
"""

import sys
sys.path.insert(0, 'tools')

import bve_compose


def reachable(T, start=0):
    seen = {start}
    work = [start]
    while work:
        s = work.pop()
        for sym in (0, 1):
            row = T.get((s, sym))
            if row is None:
                continue
            nxt = row[2]
            if nxt is not None and nxt not in seen:
                seen.add(nxt)
                work.append(nxt)
    return seen


def partition(T, live):
    part = {s: 0 for s in live}
    while True:
        sig = {}
        for s in live:
            out = []
            for sym in (0, 1):
                row = T.get((s, sym))
                if row is None:
                    out.append(('H',))
                else:
                    w, d, nxt = row
                    out.append(('R', w, d,
                                'H' if nxt is None else part[nxt]))
            sig[s] = tuple(out)
        groups = {}
        for s in live:
            groups.setdefault(sig[s], []).append(s)
        new = {}
        for i, members in enumerate(sorted(groups.values(), key=min)):
            for s in members:
                new[s] = i
        if new == part:
            return part
        part = new


def main():
    T = bve_compose.TABLE
    live = reachable(T)
    part = partition(T, live)
    classes = {}
    for s, b in part.items():
        classes.setdefault(b, []).append(s)
    multi = [c for c in classes.values() if len(c) > 1]
    print(f'BVE composed table: raw states={bve_compose.N_STATES} '
          f'rows={len(T)} reachable={len(live)} '
          f'bisim_classes={len(classes)}')
    print(f'non-singleton classes={len(multi)}')
    for c in sorted(multi, key=min):
        print('  merge:', c)
    if len(classes) >= 50:
        print('UNDER_50: NO')
    else:
        print('UNDER_50: yes (composed cursor/predecessor table only)')
    print('This is not an epsilon_1 machine: the general FS arm is semantic, '
          'and there is no blank-tape boot or index field.')


if __name__ == '__main__':
    main()
