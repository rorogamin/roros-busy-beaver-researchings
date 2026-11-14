"""Time series and left-end visits for the 6x6 champion.

Read-only.  Prints symbol counts every 2000 steps and every visit of the head
to the current leftmost non-blank cell (the likeliest home), so the macro
state can be identified from the block lengths.
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def main():
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    cap = 300_000
    left_visits = []
    last_lo = 0
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'halt at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        lo = min(tape)
        if head == lo and state in 'ABCD':
            left_visits.append((steps, state, head, dict(tape)))
        if steps % 2000 == 0:
            c = [0] * nsym
            for v in tape.values():
                c[v] += 1
            print(f'{steps:7d} {state} head={head:6d} lo={lo:6d} hi={max(tape):6d} '
                  f'nz={sum(1 for v in tape.values() if v):5d} ' +
                  ' '.join(f'{i}:{c[i]}' for i in range(nsym)))
    print(f'\nleft-end visits: {len(left_visits)}')
    for st, s, h, tp in left_visits[:60]:
        c = [0] * nsym
        for v in tp.values():
            c[v] += 1
        # rle of the non-blank region
        lo = min(tp)
        hi = max(tp)
        runs = []
        cur = None
        cnt = 0
        for p in range(lo, hi + 1):
            v = tp.get(p, 0)
            if v == cur:
                cnt += 1
            else:
                if cur is not None:
                    runs.append((cur, cnt))
                cur, cnt = v, 1
        runs.append((cur, cnt))
        r = ' '.join(f'{v}^{n}' for v, n in runs[:14])
        print(f'  step {st:>7} {s} head {h:>6} | {r}')


if __name__ == '__main__':
    main()
