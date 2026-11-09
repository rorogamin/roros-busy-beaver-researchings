import sys
sys.path.insert(0, 'tools')
import eps1_table as T
T.build_table()
rows = dict(T.TBL)
HALT = -1
states = sorted({s for s, _ in rows})
print('targets with no rows:', sorted({t for (_, _), (_, _, t) in rows.items() if t is not None and t not in states}, key=lambda s: T.SNAME[s]))
block = {s: 0 for s in states}
while True:
    sig = {}
    for s in states:
        key = []
        for sym in (0, 1):
            r = rows.get((s, sym))
            if r is None:
                key.append(None)
            else:
                w, d, t = r
                key.append((w, d, HALT if t is None else block.get(t, -2)))
        sig[s] = tuple(key)
    order = {}
    new = {}
    for s in states:
        k = sig[s]
        if k not in order:
            order[k] = len(order)
        new[s] = order[k]
    if len(order) == len({block[s] for s in states}):
        block = new
        break
    block = new
n = len({block[s] for s in states})
print('raw states', len(T.SID), 'refined (row states)', n)
groups = {}
for s, b in block.items():
    groups.setdefault(b, []).append(T.SNAME[s])
for b in sorted(groups):
    if len(groups[b]) > 1:
        print(b, groups[b])
