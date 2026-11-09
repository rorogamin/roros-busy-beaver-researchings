import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1
from eps1_table import frame, SID
T.copy_routine()
n = 2
chain = [NUM(1), 3]
p = 1
tape, E, _ = frame(p, chain, n)
print('E', E, 'tape', tm.tape_str(tape, E))
tape[E] = 0
print('after dec', tm.tape_str(tape, E-1))
t = tm.TM(len(SID), dict(T.TBL))
h, st = E-1, SID['CW0']
for i in range(60):
    print(i, T.SNAME[st], 'head', h, tm.tape_str(tape, h))
    r = t.step(tape, h, st)
    if r is None:
        print('halt'); break
    h, st = r
print('final', T.SNAME[st], h, tm.tape_str(tape, h))
print(T.decode(tape, h))
