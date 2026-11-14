"""Probe the 6x6 BB(6,6) f_{w*2} champion's macro structure.

Read-only.  Runs the machine from the blank tape and prints the tape's
run-length encoding at every new head extreme (the natural macro boundary for
a moving-head machine), plus state and symbol usage.  No level claim.
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def rle(tape, lo, hi, cap=9):
    runs = []
    cur = None
    cnt = 0
    for p in range(lo, hi + 1):
        s = tape.get(p, 0)
        if s == cur:
            cnt += 1
        else:
            if cur is not None:
                runs.append((cur, cnt))
            cur, cnt = s, 1
    if cur is not None:
        runs.append((cur, cnt))
    if len(runs) <= 2 * cap:
        return ' '.join(f'{s}^{n}' for s, n in runs)
    head = ' '.join(f'{s}^{n}' for s, n in runs[:cap])
    tail = ' '.join(f'{s}^{n}' for s, n in runs[-cap:])
    return f'{head} ... [{len(runs) - 2 * cap} runs] ... {tail}'


def main():
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    lo = hi = 0
    visits = {}
    writes = {}
    events = []
    cap = 300_000
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        visits[state] = visits.get(state, 0) + 1
        if a is None:
            print(f'halt at step {steps}, head {head}, state {state}')
            break
        w, d, nxt = a
        writes[w] = writes.get(w, 0) + 1
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        if head < lo:
            lo = head
            events.append(('L', steps, state, head, dict(tape)))
        elif head > hi:
            hi = head
            events.append(('R', steps, state, head, dict(tape)))
    print(f'steps={steps} head={head} state={state} lo={lo} hi={hi} span={hi - lo + 1}')
    print('visits: ' + ' '.join(f'{s}:{visits.get(s, 0)}' for s in 'ABCDEF'))
    print('writes: ' + ' '.join(f'{s}:{writes.get(s, 0)}' for s in range(nsym)))
    print(f'extreme events: {len(events)}')
    for side, st, s, h, tp in events[:48]:
        window = rle(tp, max(lo, h - 70), min(hi, h + 70))
        print(f'  {side} step {st:>7} {s} head {h:>7} | {window}')


if __name__ == '__main__':
    main()
