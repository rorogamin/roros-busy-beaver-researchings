"""g2probe.py — one-shot diagnostic: gate-2 failures grouped + a full trace.

Run:  python tools/g2probe.py [sn]
Prints:
  * every failing (move, start) of the seeded battery, grouped by kind;
  * a state-by-state trace of the first failing campaign.
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import random
import eps1_chain as C
import eps1_odi as O


def battery(sn):
    from eps1_super_local import chain_of, D
    T, meta = O.build_table(sn)
    rng = random.Random(17)
    fails = []
    for t_i in range(400):
        if t_i % 4 == 0:
            mp, mc = chain_of(D.tower(rng.randint(1, 3)))
        else:
            mc = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                 for _ in range(rng.randint(1, 3))]
            mp, mc = C.normalise(rng.randint(0, 2), mc)
            mc = list(mc)
        try:
            cells, h0 = O.mk_tape(mp, list(mc))
        except ValueError:
            continue
        for _m in range(4):
            try:
                p4, c4, n4, k4 = C.step(mp, list(mc), sn)
            except C.Halt:
                break
            except Exception:
                break
            k2, steps, cells2, h2 = O.campaign(dict(cells), h0, T)
            if k2 != 'rest':
                fails.append((t_i, _m, (mp, list(mc)), k2, steps))
                break
            try:
                dp, dc = O.decode_tape(cells2)
            except ValueError as e:
                fails.append((t_i, _m, (mp, list(mc)), 'DECODE', repr(e)))
                break
            if C.full(dp, dc) != C.full(p4, list(c4)):
                fails.append((t_i, _m, (mp, list(mc)), 'UNFAITHFUL',
                              ((dp, list(dc)), (p4, list(c4)))))
                break
            mp, mc = p4, list(c4)
            cells, h0 = cells2, h2
    return T, fails


def trace_first(T, fails, sn):
    from eps1_super_local import chain_of, D
    t_i, m_i, start, kind, extra = fails[0]
    rng = random.Random(17)
    mp = mc = cells = h0 = None
    hit = False
    for ti in range(400):
        if ti % 4 == 0:
            mp, mc = chain_of(D.tower(rng.randint(1, 3)))
        else:
            mc = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                 for _ in range(rng.randint(1, 3))]
            mp, mc = C.normalise(rng.randint(0, 2), mc)
            mc = list(mc)
        try:
            cells, h0 = O.mk_tape(mp, list(mc))
        except ValueError:
            continue
        for m in range(4):
            try:
                p4, c4, n4, k4 = C.step(mp, list(mc), sn)
            except C.Halt:
                break
            except Exception:
                break
            if ti == t_i and m == m_i:
                hit = True
                break
            k2, steps, cells2, h2 = O.campaign(dict(cells), h0, T)
            dp, dc = O.decode_tape(cells2)
            eq = C.full(dp, dc) == C.full(p4, list(c4))
            print(f'  move {m}: model ({mp}, {list(mc)}) -> ({p4}, {list(c4)}); '
                  f'machine rest steps={steps} decode ({dp}, {list(dc)}) '
                  f'{"=" if eq else "VALUE-MISMATCH"}')
            mp, mc = p4, list(c4)
            cells, h0 = cells2, h2
        if hit:
            break
    print(f'\nTRACE start {start} (ti={t_i}, move {m_i}, kind={kind})')
    print(f'  model step -> {k4}: ({p4}, {list(c4)})')
    print(f'  tape: ', end='')
    lo = min(min(cells), -8); hi = max(max(cells), h0 + 4)
    print(''.join(str(cells.get(x, 0)) for x in range(lo, hi + 1)))
    print(f'  head starts {h0} (scale: cell {lo} at index 0)')
    st, h = 'IN', h0
    steps = 0
    while steps < 4000:
        read = cells.get(h, 0)
        a = T.get(st, {}).get(read)
        print(f'   {steps:4d}  {st:8s} h={h:4d} read={read}  -> '
              + ('DEATH' if a is None else f'w={a[0]} {a[1]} {a[2]}'))
        if a is None:
            break
        w, d, nx = a
        cells[h] = w
        h += 1 if d == 'R' else -1
        st = nx
        steps += 1
        if st == 'IN':
            dp, dc = O.decode_tape(cells)
            print(f'   REST after {steps}: head {h}, decode ({dp}, {list(dc)})')
            return
    print(f'   (no rest within {steps} steps)')


def trace_which(T, fails, sn, which):
    from eps1_super_local import chain_of, D
    t_i, m_i, start, kind, extra = fails[which]
    rng = random.Random(17)
    mp = mc = cells = h0 = None
    hit = False
    for ti in range(400):
        if ti % 4 == 0:
            mp, mc = chain_of(D.tower(rng.randint(1, 3)))
        else:
            mc = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                 for _ in range(rng.randint(1, 3))]
            mp, mc = C.normalise(rng.randint(0, 2), mc)
            mc = list(mc)
        try:
            cells, h0 = O.mk_tape(mp, list(mc))
        except ValueError:
            continue
        for m in range(4):
            try:
                p4, c4, n4, k4 = C.step(mp, list(mc), sn)
            except C.Halt:
                break
            except Exception:
                break
            if ti == t_i and m == m_i:
                hit = True
                break
            k2, steps, cells2, h2 = O.campaign(dict(cells), h0, T)
            dp, dc = O.decode_tape(cells2)
            eq = C.full(dp, dc) == C.full(p4, list(c4))
            print(f'  move {m}: model ({mp}, {list(mc)}) -> ({p4}, {list(c4)}); '
                  f'machine steps={steps} decode ({dp}, {list(dc)}) '
                  f'{"=" if eq else "VALUE-MISMATCH"}')
            mp, mc = p4, list(c4)
            cells, h0 = cells2, h2
        if hit:
            break
    print(f'\nTRACE start {start} (ti={t_i}, move {m_i}, kind={kind})')
    print(f'  model step -> {k4}: ({p4}, {list(c4)})')
    lo = min(min(cells), -8); hi = max(max(cells), h0 + 4)
    print(f'  tape (cell=-8+i): ', end='')
    print(''.join(str(cells.get(x, 0)) for x in range(lo, hi + 1)))
    print(f'  head starts {h0}')
    st, h = 'IN', h0
    steps = 0
    while steps < 4000:
        read = cells.get(h, 0)
        a = T.get(st, {}).get(read)
        print(f'   {steps:4d}  {st:8s} h={h:4d} read={read}  -> '
              + ('DEATH' if a is None else f'w={a[0]} {a[1]} {a[2]}'))
        if a is None:
            break
        w, d, nx = a
        cells[h] = w
        h += 1 if d == 'R' else -1
        st = nx
        steps += 1
        if st == 'IN':
            dp, dc = O.decode_tape(cells)
            print(f'   REST after {steps}: head {h}, decode ({dp}, {list(dc)})')
            return
    print(f'   (no rest within {steps} steps)')


def main():
    sn = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    which = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    T, fails = battery(sn)
    kinds = {}
    for t_i, m_i, start, kind, extra in fails:
        kinds.setdefault(kind, []).append((t_i, m_i, start, extra))
    print(f'sn={sn}: {len(fails)} failures')
    for k, v in kinds.items():
        print(f'  {k}: {len(v)}')
        for row in v[:12]:
            print('   ', row)
    trace_which(T, fails, sn, which)


if __name__ == '__main__':
    main()
