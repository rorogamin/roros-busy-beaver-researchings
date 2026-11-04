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
    (0, [NUM(1), 2], 3),
    (0, [NUM(1), 1, 2], 3),
    (0, [NUM(2), 2], 3),
    (0, [ATOM, 2], 3),
    (0, [NUM(1), 2], 5),
    (0, [NUM(1), 2], 7),
]
for p, chain, n in cases:
    steps, sname, got, want = one_move(p, chain, n)
    ok = False
    if got is not None:
        def plain(ch):
            out = []
            for e in ch:
                if isinstance(e, C.Ord):
                    if e.is_atom():
                        out.append(e)
                    elif e == C.ATOM1:
                        out.append(e)
                    else:
                        out.append(e.terms[0][1])
                else:
                    out.append(e)
            return out
        ok = (got[2] == want[2] and
              C.full(got[0], plain(got[1])) == C.full(want[0], plain(want[1])))
    print(f'p={p} chain={[str(x) for x in chain]} n={n}: steps={steps} state={sname} '
          f'got={got} want={want[:3]} {"PASS" if ok else "FAIL"}')
