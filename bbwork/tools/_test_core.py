import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1

T.build_table()
t = T.machine()
HOMES = {T.SID['H0'], T.SID['H1']}


def one_move(p, chain, n):
    tape, E, home = T.frame(p, chain, n)
    st = T.SID[home]
    want = C.step(p, chain, n)
    head, steps = E, 0
    while steps < 5_000_000:
        r = t.step(tape, head, st)
        steps += 1
        if r is None:
            return steps, 'HALT', None, want
        head, st = r
        if st in HOMES:
            got = T.decode(tape, head)
            return steps, T.SNAME[st], got, want
    return steps, 'LOOP', None, want


cases = [
    (0, [NUM(2)], 3),
    (0, [ATOM1], 3),
    (0, [NUM(1), 3], 5),
    (0, [ATOM, 4], 3),
    (0, [NUM(1), 2], 3),
    (0, [NUM(1), 1, 2], 3),
    (1, [NUM(1), 3], 3),
    (2, [ATOM, 5], 3),
    (1, [NUM(1), 2], 2),
]

for p, chain, n in cases:
    try:
        steps, sname, got, want = one_move(p, chain, n)
    except Exception as e:
        print(f'p={p} chain={[str(x) for x in chain]} n={n}: RAISED {e}')
        continue
    ok = got is not None and T.same(got, (want[0], want[1], want[2]))
    print(f'p={p} chain={[str(x) for x in chain]} n={n}: steps={steps} state={sname} '
          f'got={got} want={want[:3]} {"PASS" if ok else "FAIL"}')
