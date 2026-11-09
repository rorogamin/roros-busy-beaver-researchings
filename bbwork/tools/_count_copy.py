import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
from eps1_chain import NUM
T.build_table()
t = T.machine()
n = 3
chain = [NUM(1), 3]
tape, E, _ = T.frame(1, chain, n)
tape[E] = 0
steps, t2, h2, s2, halted = T.run_to(t, E - 1, T.SID['CW0'], tape, {T.SID['SP0']})
print('E', E, 'halted', halted, 'state', T.SNAME[s2], 'head', h2)
print(tm.tape_str(t2, h2))
print(T.decode(t2, h2))
# print runs right of E
x = E
print('E still', E)
print([t2.get(i,0) for i in range(E-2, E+15)])
