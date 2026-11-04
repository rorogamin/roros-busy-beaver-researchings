import sys
sys.path.insert(0, 'tools')
import eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1

T.build_table()
p, chain, n = 0, [NUM(1), 1, 2], 3
tape, E, home = T.frame(p, chain, n)
t = T.machine()
head, st = E, T.SID[home]
homes = {T.SID['H0'], T.SID['H1']}
cur_v = C.full(p, T.plain_chain(list(chain)))
prev_v = cur_v
steps = trips = adv = extra = 0
records = []
while steps < 2_000_000:
    r = t.step(tape, head, st)
    steps += 1
    if r is None:
        print('HALT after', steps, 'trips', trips, 'adv', adv, 'extra', extra)
        break
    head, st = r
    if st in homes:
        trips += 1
        got = T.decode(tape, head)
        gv = C.full(got[0], T.plain_chain(got[1]))
        if gv == prev_v:
            extra += 1
            records.append(('extra', trips, got))
        else:
            adv += 1
            prev_v = gv
            records.append(('adv', trips, got))
print('final adv', adv, 'halt counts as 1 =>', adv + 1)
for rec in records[:6]:
    print(rec)
print('...')
for rec in records[-6:]:
    print(rec)
