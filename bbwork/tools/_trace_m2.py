import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1

T.build_table()
t = T.machine()
p, chain, n = 0, [NUM(1), 1, 2], 3
tape, E, home = T.frame(p, chain, n)
head, st = E, T.SID[home]
homes = {T.SID['H0'], T.SID['H1']}
print('start', home, E, tm.tape_str(tape, head))
for mv in range(4):
    print('--- model', C.step(p, chain, n)[:3])
    steps = 0
    while steps < 100000:
        print(f'{steps:4d} {T.SNAME[st]:5s} {head:3d} {tape.get(head,0)} '
              f'{tm.tape_str(tape, head)}')
        r = t.step(tape, head, st)
        steps += 1
        if r is None:
            print('HALT')
            break
        head, st = r
        if st in homes:
            print(f'--- home {T.SNAME[st]} at {head} after {steps}')
            print('    decode', T.decode(tape, head))
            p, chain, n = T.decode(tape, head)
            break
    else:
        print('LOOP')
        break
