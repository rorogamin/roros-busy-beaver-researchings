import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1
import eps1_minimise as M

T.build_table()
rows = dict(T.TBL)
start = 0
block, n = M.blocks_of(rows)
mini, mstart, n = M.rebuild(rows, start)
states = len({s for s, _ in rows})
print(f'raw: {states} states, {len(rows)} rows')
print(f'refined: {n} states, {len(mini)} rows')
groups = {}
for s, b in block.items():
    groups.setdefault(b, []).append(s)
print('nontrivial classes:', sum(1 for g in groups.values() if len(g) > 1))
for b, g in sorted(groups.items()):
    if len(g) > 1:
        print('  ', b, [T.SNAME[x] for x in sorted(g)])


def run_pair(tape, head, state, steps):
    a = tm.TM(len(T.SID), dict(rows))
    b = tm.TM(n, dict(mini))
    ta, ha, sa = dict(tape), head, state
    tb, hb, sb = dict(tape), head, block[state]
    for i in range(steps):
        ra = a.step(ta, ha, sa)
        rb = b.step(tb, hb, sb)
        if (ra is None) != (rb is None):
            return f'halt mismatch at step {i}'
        if ra is None:
            break
        ha, sa = ra
        hb, sb = rb
        if ha != hb or ta != tb:
            return f'tape/head mismatch at step {i}'
    if ta != tb:
        return 'final tape mismatch'
    return None


bad = 0
# blank-tape build
err = run_pair({}, 0, 0, 16)
print('blank build:', err or 'OK')
bad += err is not None
# frames and a few moves
cases = [(0, [ATOM], 3), (0, [ATOM1], 3), (2, [ATOM1, 2, 4], 1),
         (0, [NUM(1), 1, 2], 3), (1, [NUM(2), 2], 4), (3, [NUM(1)], 1)]
for p, c, n0 in cases:
    tape, E, home = T.frame(p, c, n0)
    err = run_pair(tape, E, T.SID[home], 300)
    print('frame', [str(x) for x in c], 'p', p, 'n', n0, ':', err or 'OK')
    bad += err is not None
print('ALL OK' if bad == 0 else f'{bad} FAILURES')
