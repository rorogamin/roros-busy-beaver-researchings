import sys
from collections import deque
sys.path.insert(0, 'tools')
import tm, eps1_table as T
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1

T.build_table()
t = T.machine()
CASE = (3, [NUM(1)], 1)
if len(sys.argv) > 1:
    CASE = eval(sys.argv[1])
p, chain, n = CASE
tape, E, home = T.frame(p, chain, n)
head, st = E, T.SID[home]
homes = {T.SID['H0'], T.SID['H1']}
cur = (p, list(chain), n)


def win(tape, head, w=10):
    lo, hi = head - w, head + w
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    return s[:w] + '<' + s[w] + '>' + s[w + 1:]


for mv in range(4):
    want = C.step(*cur)[:3]
    print(f'=== model move {mv+1}: {cur[:2]} n={cur[2]} -> {want[:2]} n={want[2]}')
    extra = 0
    while True:
        history = deque(maxlen=120)
        steps = 0
        while steps < 100_000:
            history.append((steps, st, head, tape.get(head, 0), win(tape, head, 5)))
            r = t.step(tape, head, st)
            steps += 1
            if r is None:
                print('HALT at', steps)
                raise SystemExit
            head, st = r
            if st in homes:
                break
            if abs(head) > 500:
                print('RUNAWAY at', steps, T.SNAME[st], head)
                for rec in list(history)[-90:]:
                    print('  ', rec[0], T.SNAME[rec[1]], rec[2], rec[3], rec[4])
                raise SystemExit
        else:
            print('LOOP at', T.SNAME[st], head)
            for rec in list(history)[-90:]:
                print('  ', rec[0], T.SNAME[rec[1]], rec[2], rec[3], rec[4])
            raise SystemExit
        got = T.decode(tape, head)
        gv = C.full(got[0], T.plain_chain(got[1]))
        wv = C.full(want[0], T.plain_chain(want[1]))
        cv = C.full(cur[0], T.plain_chain(cur[1]))
        print('  home', T.SNAME[st], 'head', head, 'steps', steps, 'got', got)
        if got[2] == want[2] and gv == wv:
            print('  MATCH')
            cur = want
            break
        if got[2] == cur[2] and gv == cv:
            extra += 1
            print('  normalisation-only', extra)
            if extra > 8:
                print('  too many')
                raise SystemExit
            continue
        print('  MISMATCH got', gv, 'want', wv)
        raise SystemExit
    if not cur[1]:
        break
