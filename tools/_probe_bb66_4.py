"""Visits to the 4 level marker and the marker's position over time."""

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
    prev4 = None
    visits = []
    changes = 0
    while steps < 300_000:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'halt at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        p4 = [p for p, v in tape.items() if v == 4]
        if p4 != prev4:
            changes += 1
            if changes <= 20 or steps % 50000 < 100:
                print(f'4 position {p4} at step {steps} ({state})')
            prev4 = p4
        if p4 and head == p4[0]:
            visits.append((steps, state, head, dict(tape)))
    print(f'\n4-position changes: {changes}; visits to the marker: {len(visits)}')
    sample = visits[:40] + visits[40::max(1, len(visits) // 20)] if len(visits) > 40 else visits
    for st, s, h, tp in sample[:60]:
        c = [0] * nsym
        for v in tp.values():
            c[v] += 1
        lo, hi = min(tp), max(tp)
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
        r = ' '.join(f'{v}^{n}' for v, n in runs[:10])
        print(f'  step {st:>7} {s} head {h:>6} counts ' +
              ' '.join(f'{i}:{c[i]}' for i in range(nsym)) + f' | {r}')


if __name__ == '__main__':
    main()
