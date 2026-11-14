"""A 44-state minimisation of the BVE cursor + predecessor table.

`bve_compose.py` is a 46-state raw table.  Two of its states are unreachable
from the entry, and states 10/11 have identical two-symbol rows, so the
reachable Moore quotient has 44 states.  This module builds that quotient
without editing the raw table and re-runs the composition's 409-term checks
through the quotient.

Scope: this is the **active-site cursor + predecessor** table, not a full
epsilon_1 machine.  It has no blank-tape boot, no index field, and no general
FS rewrite arm.  The 44-state count is a measured table count for what the
table actually does.

Run: python tools/bve_compose44.py
"""

import sys
sys.path.insert(0, 'tools')

import bve_compose


def _reachable(T, start=0):
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


def _partition(T, live):
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


def _quotient(T, part):
    """Class id -> canonical state number, entry class first."""
    classes = {}
    for s, b in part.items():
        classes.setdefault(b, []).append(s)
    order = sorted(classes.values(), key=min)
    # The entry state is 0; its class must become state 0.
    entry_block = part[0]
    order.sort(key=lambda members: (part[members[0]] != entry_block, min(members)))
    cid = {}
    rep = {}
    for i, members in enumerate(order):
        rep[i] = min(members)
        for s in members:
            cid[s] = i
    out = {}
    for i, members in enumerate(order):
        s = rep[i]
        for sym in (0, 1):
            row = T.get((s, sym))
            if row is None:
                continue
            w, d, nxt = row
            out[(i, sym)] = (w, d, None if nxt is None else cid[nxt])
    return out, len(order), len(classes)


def build_table():
    table, n, nclasses = _quotient(bve_compose.TABLE,
                                   _partition(bve_compose.TABLE,
                                              _reachable(bve_compose.TABLE)))
    return table, n, nclasses


TABLE, N_STATES, N_CLASSES = build_table()
assert N_STATES == 44, N_STATES


def check():
    # bve_compose.run() and its checkers look up TABLE/N_STATES at call time.
    old_table, old_n = bve_compose.TABLE, bve_compose.N_STATES
    bve_compose.TABLE, bve_compose.N_STATES = TABLE, N_STATES
    try:
        ok = bve_compose.check()
        ok = bve_compose.check_raw_chain() and ok
    finally:
        bve_compose.TABLE, bve_compose.N_STATES = old_table, old_n
    return ok


def main():
    print(f'BVE cursor+pred quotient: {N_STATES} states, '
          f'{len(TABLE)} rows, {N_CLASSES} classes')
    ok = check()
    if ok:
        print()
        print('scope: cursor + predecessor only; no boot, index, or general FS')
        print('UNDER_50: yes')
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
