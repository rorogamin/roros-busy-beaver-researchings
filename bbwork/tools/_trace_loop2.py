import sys
from collections import deque
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


def win(tape, head, w=12):
    lo, hi = head - w, head + w
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    return s[:w] + '<' + s[w] + '>' + s[w + 1:]


def run_one(cur, tape, head, st, want):
    cv = C.full(cur[0], T.plain_chain(cur[1]))
    wv = C.full(want[0], T.plain_chain(want[1]))
    extra = 0
    while True:
        history = deque(maxlen=140)
        steps = 0
        while steps < 50_000:
            history.append((steps, st, head, tape.get(head, 0)))
            r = t.step(tape, head, st)
            steps += 1
            if r is None:
                return 'HALT', steps, None, head, st
            head, st = r
            if st in homes:
                break
            if head > E + 200:
                print('  runaway; last 70 states:')
                for rec in list(history)[-70:]:
                    print('   ', rec[0], T.SNAME[rec[1]], rec[2], rec[3])
                print('   tape', win(tape, head, 8))
                return 'RUNAWAY', steps, None, head, st
        else:
            print('  step limit; last 70 states:')
            for rec in list(history)[-70:]:
                print('   ', rec[0], T.SNAME[rec[1]], rec[2], rec[3])
            return 'LOOP', steps, None, head, st
        got = T.decode(tape, head)
        gv = C.full(got[0], T.plain_chain(got[1]))
        print('  home', T.SNAME[st], 'head', head, 'steps', steps, 'got', got)
        if got[2] == want[2] and gv == wv:
            return 'MATCH', steps, got, head, st
        if got[2] == cur[2] and gv == cv:
            extra += 1
            print('   normalisation-only, extra', extra)
            if extra > 6:
                return 'TOO MANY EXTRA', steps, got, head, st
            continue
        print('   got value', gv)
        print('   want value', wv)
        return 'MISMATCH', steps, got, head, st


for mv in range(5):
    if not cur[1]:
        break
    want = C.step(*cur)[:3]
    print(f'=== model move {mv+1}: {cur[:2]} n={cur[2]} -> {want[:2]} n={want[2]}')
    status, steps, got, head, st = run_one(cur, tape, head, st, want)
    print('  ->', status, steps, 'head', head, 'state', T.SNAME[st])
    if status != 'MATCH':
        break
    cur = want
