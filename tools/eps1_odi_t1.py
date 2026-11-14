"""A run-specialized odometer table for the tier-1 campaign (61 states).

This is the odometer pivot, not the BVE table.  Start from the general
71-state `eps1_odi` build (sn=1), trace the exact tier-1 run
`chain_of(D.tower(1))`, retain only the rows that run fires, prune to the
reachable states, and apply the two observed-context merges that survive:

    CM4 -> CM1
    D5  -> D3

The result is 63 reached states / 89 rows before context merging and 61
states after it.  It is checked move-for-move against `eps1_chain.step` for
the tier-1 sequence only.  It is NOT the general odometer: rows outside that
run are deliberately absent, and no FGH claim is made.  A finite-run Rocq
certificate is generated separately by `emit_eps1_odi_t1_rocq.py`.

Run: python tools/eps1_odi_t1.py
"""

import sys
sys.path.insert(0, 'tools')

import eps1_odi as O
from eps1_super_local import chain_of, D


def _prune(T):
    live = O._reachable(T, 'IN')
    return {s: dict(T[s]) for s in live}


def _retarget(T, y, x):
    out = {s: dict(rows) for s, rows in T.items()}
    if y not in out:
        raise AssertionError(f'missing merge source {y}')
    del out[y]
    for rows in out.values():
        for sym, (w, d, nxt) in list(rows.items()):
            if nxt == y:
                rows[sym] = (w, d, x)
    return _prune(out)


def trace_rows(T, tier=1):
    """Rows and states fired by the exact tier-1 model walk."""
    mp, mc = chain_of(D.tower(tier))
    fired = set()
    while mc:
        cells, h = O.mk_tape(mp, list(mc))
        st = 'IN'
        for _ in range(400_000):
            sym = cells.get(h, 0)
            fired.add((st, sym))
            a = T.get(st, {}).get(sym)
            if a is None:
                break
            w, d, nx = a
            cells[h] = w
            h += 1 if d == 'R' else -1
            st = nx
            if st == 'IN':
                break
        try:
            dp, dc = O.decode_tape(cells)
        except Exception:
            break
        try:
            p2, c2, _, _ = O.C.step(mp, list(mc), 1)
        except O.C.Halt:
            break
        mp, mc = p2, list(c2)
    return fired


def build_table():
    T, _meta = O.build_table(1)
    fired = trace_rows(T)
    sub = {s: {sym: T[s][sym] for sym in T[s] if (s, sym) in fired}
           for s in T}
    sub = _prune(sub)
    sub, _meta = O.minimise_table(sub, {s: '' for s in sub}, 'IN')
    sub = _retarget(sub, 'CM4', 'CM1')
    sub, _meta = O.minimise_table(sub, {s: '' for s in sub}, 'IN')
    sub = _retarget(sub, 'D5', 'D3')
    sub, _meta = O.minimise_table(sub, {s: '' for s in sub}, 'IN')
    return sub


def check(T):
    mp, mc = chain_of(D.tower(1))
    moves = 0
    while mc:
        cells, h = O.mk_tape(mp, list(mc))
        k, steps, cells2, _h2 = O.campaign(cells, h, T)
        if k != 'rest':
            print(f'  tier-1 campaign stopped: {k}')
            return False
        try:
            dp, dc = O.decode_tape(cells2)
        except ValueError as e:
            print(f'  tier-1 decode failed: {e}')
            return False
        try:
            p2, c2, _, _ = O.C.step(mp, list(mc), 1)
        except O.C.Halt:
            break
        if O.C.full(dp, dc) != O.C.full(p2, list(c2)):
            print('  tier-1 landing mismatch')
            return False
        mp, mc = p2, list(c2)
        moves += 1
    print(f'  tier-1: {moves} moves, model-equal')
    return moves == 9


def main():
    T = build_table()
    print(f'eps1_odi_t1: states={len(T)} rows={sum(len(r) for r in T.values())}')
    ok = check(T)
    if ok:
        print('  scope: exact tier-1 run only; not the general odometer')
        print('  no FGH claim; Rocq certificate is emitted separately')
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
