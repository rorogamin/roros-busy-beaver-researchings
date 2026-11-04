import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM

T.build_table()
t = T.machine()
HOMES = {T.SID['H0'], T.SID['H1']}

for p in (1, 2, 3):
    for n in (3, 4):
        tape, E, home = T.frame(p, [NUM(1)], n)
        st = T.SID[home]
        want = C.step(p, [NUM(1)], n)
        head, steps = E, 0
        while steps < 5_000_000:
            r = t.step(tape, head, st)
            steps += 1
            if r is None:
                print('HALT', p, n, steps, tm.tape_str(tape, head)); break
            head, st = r
            if st in HOMES:
                got = T.decode(tape, head)
                ok = (got[0] == want[0] and got[2] == want[2] and
                      T.same((got[0], got[1], got[2]), (want[0], want[1], want[2])))
                print(f'p={p} n={n}: steps={steps} {T.SNAME[st]} got={got} '
                      f'want={want[:3]} {"PASS" if ok else "FAIL"}')
                break
        else:
            print('LOOP', p, n)
