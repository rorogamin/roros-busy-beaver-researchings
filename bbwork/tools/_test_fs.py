import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM

T.build_table()
t = T.machine()
HOMES = {T.SID['H0'], T.SID['H1']}


def one_move(p, chain, n):
    tape, E, home = T.frame(p, chain, n)
    st = T.SID[home]
    want = C.step(p, chain, n)
    head, steps = E, 0
    while steps < 2_000_000:
        r = t.step(tape, head, st)
        steps += 1
        if r is None:
            return steps, 'HALT', None, want
        head, st = r
        if st in HOMES:
            got = T.decode(tape, head)
            return steps, T.SNAME[st], got, want
    return steps, 'LOOP', None, want


bad = 0
for p in (0, 1, 2):
    for n in (1, 2, 3, 4):
        steps, sname, got, want = one_move(p, [ATOM], n)
        ok = (got is not None and T.same(got, (want[0], want[1], want[2])))
        if not ok:
            bad += 1
        print(f'p={p} n={n}: steps={steps} state={sname} got={got} '
              f'want={want[:3]} {"PASS" if ok else "FAIL"}')
print('bad', bad)
