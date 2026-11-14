"""Phase probe: counts and tape layout of the 6x6 champion at intervals.

Read-only.  Usage: python tools/_probe_bb66_phase.py [cap]
Prints the symbol counts every cap/10 steps, the marker changes, and the final
run-length encoding, so the long growth phase can be read off directly.
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 50_000_000
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    p4, p5 = set(), set()
    last4, last5 = (), ()
    changes4 = changes5 = 0
    next_sample = cap // 10

    def counts():
        c = [0] * nsym
        for v in tape.values():
            c[v] += 1
        return c

    def counts_str():
        c = counts()
        return ' '.join(f'{i}:{c[i]}' for i in range(1, nsym))

    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'HALT at {steps} state={state} head={head}')
            break
        w, d, nxt = a
        old = tape.get(head, 0)
        tape[head] = w
        if old == 4:
            p4.discard(head)
        if old == 5:
            p5.discard(head)
        if w == 4:
            p4.add(head)
        if w == 5:
            p5.add(head)
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        t4, t5 = tuple(sorted(p4)), tuple(sorted(p5))
        if t4 != last4:
            changes4 += 1
            if changes4 <= 12 or changes4 % 100 == 0:
                print(f'4change {steps} {state} h={head} 4={t4}  {counts_str()}')
            last4 = t4
        if t5 != last5:
            changes5 += 1
            if changes5 <= 12 or changes5 % 50 == 0:
                print(f'5change {steps} {state} h={head} 5={t5}  {counts_str()}')
            last5 = t5
        if steps >= next_sample:
            print(f'sample {steps} {state} h={head}  {counts_str()}  '
                  f'span={max(tape) - min(tape) + 1}')
            next_sample += cap // 10

    lo, hi = min(tape), max(tape)
    print(f'final steps={steps} state={state} head={head} span={hi - lo + 1} '
          f'nz={sum(1 for v in tape.values() if v)}  {counts_str()}')
    print(f'changes: 4={changes4} 5={changes5}')

    runs = []
    cur = tape.get(lo, 0)
    n = 1
    start = lo
    for p in range(lo + 1, hi + 1):
        v = tape.get(p, 0)
        if v == cur:
            n += 1
        else:
            runs.append((cur, n, start))
            cur, n, start = v, 1, p
    runs.append((cur, n, start))
    # merge adjacent runs of the same symbol (none expected) and print compactly
    print('rle:', [(s, n, st, st + n - 1) for (s, n, st) in runs])


if __name__ == '__main__':
    main()
