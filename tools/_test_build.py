import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
from eps1_chain import ATOM1

T.build_table()
t = T.machine()
print('state 0 is', T.SNAME.get(0), 'start', T.SNAME[T.SID['BU0']])
head, st, tape = 0, 0, {}
HOMES = {T.SID['H0'], T.SID['H1']}
steps = 0
while steps < 10000:
    r = t.step(tape, head, st)
    steps += 1
    if r is None:
        print('HALT at', steps, tm.tape_str(tape, head))
        break
    head, st = r
    if st in HOMES:
        got = T.decode(tape, head)
        print('home', T.SNAME[st], 'head', head, 'steps', steps,
              'tape', tm.tape_str(tape, head))
        print('got', got)
        print('PASS' if T.same(got, (3, [ATOM1], 3)) else 'FAIL')
        break
else:
    print('LOOP')
