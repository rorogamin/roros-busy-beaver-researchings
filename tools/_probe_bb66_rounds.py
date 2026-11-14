"""Round tracer: the 6x6 champion at new head extremes.

Read-only.  Each new global extreme is one macro boundary (the same segmentation
as _check_bb66_omega2.py).  Prints the counts and the 4/5 positions so the
round rule and the field deltas can be read off.
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
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
    table, nst, nsym = parse(SPEC)
    tape = {}
    head = 0
    state = 'A'
    steps = 0
    lo = hi = 0
    events = []
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print(f'HALT at {steps}')
            break
        w, d, nxt = a
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        if head < lo or head > hi:
            lo = min(lo, head)
            hi = max(hi, head)
            p4 = sorted(p for p, v in tape.items() if v == 4)
            p5 = sorted(p for p, v in tape.items() if v == 5)
            events.append((steps, state, head, counts(tape, nsym), p4, p5,
                           lo, hi))

    def line(e):
        st, s, h, c, p4, p5, l, r = e
        return (f'{st:>8} {s} h={h:>6} 1:{c[1]:>5} 2:{c[2]:>3} '
                f'3:{c[3]:>5} 4:{c[4]} 5:{c[5]} '
                f'4@{p4} 5@{p5} ext=[{l},{r}]')

    print(f'cap={cap} events={len(events)}')
    print('\nfirst 40')
    for e in events[:40]:
        print('  ' + line(e))
    if len(events) > 60:
        print('\nmiddle sample')
        step = max(1, (len(events) - 60) // 20)
        for e in events[40:-20:step]:
            print('  ' + line(e))
    print('\nlast 20')
    for e in events[-20:]:
        print('  ' + line(e))

    print('\nlargest field moves between consecutive events')
    scored = []
    for i in range(1, len(events)):
        d1 = events[i][3][1] - events[i - 1][3][1]
        d2 = events[i][3][2] - events[i - 1][3][2]
        d3 = events[i][3][3] - events[i - 1][3][3]
        if abs(d1) + abs(d2) + abs(d3) >= 4:
            scored.append((abs(d1) + abs(d2) + abs(d3), i, d1, d2, d3))
    for mag, i, d1, d2, d3 in sorted(scored, reverse=True)[:20]:
        st = events[i]
        print(f'  at {st[1]} {st[2]:>7}: d1={d1:+} d2={d2:+} d3={d3:+}  '
              f'1:{st[3][1]} 2:{st[3][2]} 3:{st[3][3]}')


if __name__ == '__main__':
    main()
