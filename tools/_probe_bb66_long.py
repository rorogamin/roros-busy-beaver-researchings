"""Long probe: the 6x6 champion's 4/5 marker boundaries to 10M steps.

Read-only.  Tracks the marker positions incrementally, so the run stays linear,
and prints the symbol counts at every 4-position change (the level boundary).
"""

import sys

sys.path.insert(0, 'tools')

from bbmulti import parse

SPEC = ('4LF3LB1RZ2RA4LB---_2LC3RB1LD2RA3LF---_3RB1LB3LC2RC4LC0LE_'
        '3RB---3LC2RC---3RE_5RC3RE---4LC------_5RB0LF1RB1LF---5RB')


def counts(tape, nsym):
    c = [0] * nsym
    for v in tape.values():
        c[v] += 1
    return c


def main():
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    p4, p5 = set(), set()
    prev4, prev5 = (), ()
    bounds, fives = [], []
    cap = 10_000_000
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'halt at {steps}')
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
        if t4 != prev4:
            bounds.append((steps, state, head, t4, counts(tape, nsym)))
            prev4 = t4
        if t5 != prev5:
            fives.append((steps, state, head, t5, counts(tape, nsym)))
            prev5 = t5

    lo, hi = min(tape), max(tape)
    print(f'steps={steps} head={head} state={state} span={hi - lo + 1} '
          f'nz={sum(1 for v in tape.values() if v)}')
    print(f'4-position changes={len(bounds)}  5-position changes={len(fives)}')

    def line(b):
        st, s, h, t4, c = b
        return (f'{st:>9} {s} h={h:>7} 4={t4} '
                f'1:{c[1]} 2:{c[2]} 3:{c[3]} 4:{c[4]} 5:{c[5]}')

    print('\nfirst 40 four-boundaries')
    for b in bounds[:40]:
        print('  ' + line(b))
    if len(bounds) > 60:
        print('\nmiddle sample')
        step = max(1, (len(bounds) - 60) // 20)
        for b in bounds[40:-20:step]:
            print('  ' + line(b))
    print('\nlast 20 four-boundaries')
    for b in bounds[-20:]:
        print('  ' + line(b))

    print('\n5-marker changes (first 12, last 8)')
    for b in fives[:12] + (fives[-8:] if len(fives) > 12 else []):
        print('  ' + line(b))


if __name__ == '__main__':
    main()
