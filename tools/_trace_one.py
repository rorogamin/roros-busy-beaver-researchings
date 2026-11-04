import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
from eps1_chain import NUM
T.build_table()
t = T.machine()
tape, E, home = T.frame(0, [NUM(2)], 3)
print('E', E, 'home', home, tm.tape_str(tape, E))
h, st = E, T.SID[home]
for i in range(30):
    print(i, T.SNAME[st], h, 'sym', tape.get(h, 0), tm.tape_str(tape, h))
    r = t.step(tape, h, st)
    if r is None:
        print('HALT'); break
    h, st = r
