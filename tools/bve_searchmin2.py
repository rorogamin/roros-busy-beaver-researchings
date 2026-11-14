"""Search below the 39-state BVE quotient.

This starts from `bve_compose39`, not the 44-state table, and uses the same
wide corpus and beam mechanism as `bve_searchmin.py`.  A candidate is kept
only if it preserves the 39-state reference output on the training corpus;
any table below 39 is then run through the full 409-term BVE check.

Scope: cursor + predecessor only.  No general FS.

Run: python tools/bve_searchmin2.py
"""

import sys
sys.path.insert(0, 'tools')

import bve_compose39
import bve_searchmin as S


def main():
    data = S.make_corpus()
    base = dict(bve_compose39.TABLE)
    ref = S.fingerprint(base, data)
    assert ref is not None
    print(f'corpus={len(data)}; reference 39 states')
    starts = [(39, base, ())]
    seen = {S.table_key(base)}
    best = (39, base, ())
    beam = 64
    for depth in range(1, 9):
        nxt = []
        for n, table, path in starts:
            for y, x in S.candidates(table, data):
                trial = S.merge(table, y, x)
                t2, n2, _ = S.exact_quotient(trial)
                if n2 >= n:
                    continue
                key = S.table_key(t2)
                if key in seen:
                    continue
                seen.add(key)
                if S.fingerprint(t2, data) != ref:
                    continue
                if n2 < best[0]:
                    best = (n2, t2, path + ((y, x),))
                    print(f'  depth {depth}: {n2} states, path {best[2]}')
                if n2 < 39:
                    if not S.accepts_std(t2, n2):
                        print(f'    full check rejected {n2}')
                        continue
                    S.emit_module(t2, n2)
                    print(f'FOUND {n2} states; wrote tools/bve_compose{n2}.py')
                    return 0
                nxt.append((n2, t2, path + ((y, x),)))
        if not nxt:
            break
        nxt.sort(key=lambda z: (z[0], S.table_key(z[1])))
        starts = nxt[:beam]
        print(f'  depth {depth}: frontier {len(nxt)}, best {starts[0][0]}')
    print(f'no sub-39 table; best {best[0]} states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
