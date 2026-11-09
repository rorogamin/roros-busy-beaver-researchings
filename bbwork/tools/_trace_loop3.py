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


def win(tape, head, w=10):
    lo, hi = head - w, head + w
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    return s[:w] + '<' + s[w] + '>' + s[w + 1:]


for mv in range(4):
    want = C.step(*cur)[:3]
    print(f'=== model move {mv+1}: {cur[:2]} n={cur[2]} -> {want[:2]} n={want[2]}')
    # run to first home
    steps = 0
    while steps < 100_000:
        if mv == 3 and steps < 140:
            print(f'{steps:4d} {T.SNAME[st]:5s} {head:3d} {tape.get(head,0)} {win(tape, head)}')
        r = t.step(tape, head, st)
        steps += 1
        if r is None:
            print('HALT at', steps)
            raise SystemExit
        head, st = r
        if st in homes:
            break
    else:
        print('LOOP at', T.SNAME[st], head)
        raise SystemExit
    got = T.decode(tape, head)
    gv = C.full(got[0], T.plain_chain(got[1]))
    wv = C.full(want[0], T.plain_chain(want[1]))
    cv = C.full(cur[0], T.plain_chain(cur[1]))
    print('  home', T.SNAME[st], 'head', head, 'steps', steps, 'got', got)
    if got[2] == want[2] and gv == wv:
        print('  MATCH')
        cur = want
        if mv == 3:
            break
    elif got[2] == cur[2] and gv == cv:
        print('  normalisation-only; replay the same model move')
        # do not advance mv: rerun from this home against the same want
        # (handled by the outer while below)
        while True:
            steps = 0
            while steps < 100_000:
                r = t.step(tape, head, st)
                steps += 1
                if r is None:
                    print('HALT at', steps)
                    raise SystemExit
                head, st = r
                if st in homes:
                    break
            got = T.decode(tape, head)
            gv = C.full(got[0], T.plain_chain(got[1]))
            print('  extra home', T.SNAME[st], 'head', head, 'steps', steps, 'got', got)
            if got[2] == want[2] and gv == wv:
                print('  MATCH after normalisation')
                cur = want
                break
            if got[2] == cur[2] and gv == cv:
                continue
            print('  MISMATCH')
            raise SystemExit
    else:
        print('  MISMATCH')
        print('   got value', gv)
        print('   want value', wv)
        break
