"""Fine trace around the first level transition (5 disappears, 4 appears)."""

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
    hist = []
    prev5 = 0
    cap = 40_000
    while steps < cap:
        a = table.get((state, tape.get(head, 0)))
        if a is None:
            print('halt')
            break
        w, d, nxt = a
        hist.append((steps, state, head, tape.get(head, 0), w, d, nxt,
                     [p for p, v in tape.items() if v == 4],
                     [p for p, v in tape.items() if v == 5]))
        if len(hist) > 80:
            hist.pop(0)
        tape[head] = w
        steps += 1
        head += 1 if d == 'R' else -1
        state = nxt
        c5 = sum(1 for v in tape.values() if v == 5)
        if prev5 == 1 and c5 == 0 and steps > 1000:
            print(f'5 erased at step {steps}')
            for st, s, h, rd, wr, dr, nx, p4, p5 in hist:
                print(f'  {st:>6} {s} head {h:>4} read {rd} -> {wr}{dr}{nx}'
                      f'  4@{p4} 5@{p5}')
            break
        prev5 = c5


if __name__ == '__main__':
    main()
