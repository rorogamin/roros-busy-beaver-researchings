"""Beam search below an arbitrary BVE quotient.

Usage: python tools/bve_searchmin_any.py <module> <target>
Example: python tools/bve_searchmin_any.py bve_compose38 38

The module must expose N_STATES and TABLE.  The search uses the wide corpus
and screening from `bve_searchmin`; a table below the target is accepted only
after the full 409-term BVE check.

Scope: cursor + predecessor only.  No general FS.
"""

import importlib
import sys
sys.path.insert(0, 'tools')

import bve_searchmin as S


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    mod = importlib.import_module(sys.argv[1])
    target = int(sys.argv[2])
    data = S.make_corpus()
    base = dict(mod.TABLE)
    ref = S.fingerprint(base, data)
    assert ref is not None
    n0 = mod.N_STATES
    print(f'corpus={len(data)}; start={sys.argv[1]} ({n0} states), '
          f'target<{target}')
    starts = [(n0, base, ())]
    seen = {S.table_key(base)}
    best = (n0, base, ())
    beam = 64
    for depth in range(1, 10):
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
                if n2 < target:
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
    print(f'no table below {target}; best {best[0]} states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
