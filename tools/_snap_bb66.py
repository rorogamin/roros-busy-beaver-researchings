"""Full block layout of the 6x6 champion at fixed step milestones."""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')

TARGETS = {22_000, 50_000, 100_000, 120_000, 200_000, 300_000}


def main():
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    while steps <= max(TARGETS):
        if steps in TARGETS:
            lo, hi = min(tape), max(tape)
            runs = []
            cur = None
            cnt = 0
            for p in range(lo, hi + 1):
                v = tape.get(p, 0)
                if v == cur:
                    cnt += 1
                else:
                    if cur is not None:
                        runs.append((cur, cnt))
                    cur, cnt = v, 1
            runs.append((cur, cnt))
            r = ' '.join(f'{v}^{n}' for v, n in runs[:24])
            c = [0] * nsym
            for v in tape.values():
                c[v] += 1
            print(f'{steps}: {state} head={head} lo={lo} hi={hi} '
                  f'nz={sum(1 for v in tape.values() if v)}')
            print(f'   {r}')
            print('   counts ' + ' '.join(f'{i}:{c[i]}' for i in range(nsym)))
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'halt at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt


if __name__ == '__main__':
    main()
