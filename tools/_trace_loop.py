import sys
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1

T.build_table()
t = T.machine()
p, chain, n = 2, [ATOM1, 2, 4], 1
tape, E, home = T.frame(p, chain, n)
head, st = E, T.SID[home]
homes = {T.SID['H0'], T.SID['H1']}
cur = (p, list(chain), n)


def win(tape, head, w=8):
    lo, hi = head - w, head + w
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    return s[:w] + '<' + s[w] + '>' + s[w + 1:]


print('start', win(tape, head), 'E', E)
for mv in range(5):
    if not cur[1]:
        break
    want = C.step(*cur)[:3]
    print(f'=== model move {mv+1}: {cur[:2]} -> {want}')
    steps = 0
    last = None
    while steps < 300_000:
        if steps % 20_000 == 0 and steps:
            print('  ...', steps, T.SNAME[st], head, win(tape, head))
        r = t.step(tape, head, st)
        steps += 1
        last = (st, head)
        if r is None:
            print('HALT after', steps)
            break
        head, st = r
        if st in homes:
            got = T.decode(tape, head)
            print(f'home {T.SNAME[st]} at {head} steps {steps}: {got}')
            if T.same(got, want):
                cur = want
            elif C.full(got[0], T.plain_chain(got[1])) == C.full(cur[0], T.plain_chain(cur[1])):
                print('  (normalisation-only)')
            else:
                print('  MISMATCH')
                cur = want
            break
    else:
        print('STEPS LIMIT at state', T.SNAME[st], 'head', head)
        print(win(tape, head, 20))
        print('last', last)
        break
    if r is None:
        break
