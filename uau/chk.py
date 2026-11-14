#!/usr/bin/env python3
"""focused tests: build a tape by hand, start the checker, report the verdict."""
import sys
sys.path.insert(0, '.')
import uubin as U


def tape_for(seq, cand):
    cells = list(U.group(U.WALL))
    for v in list(seq) + [cand]:
        cells += U.group(U.PLAIN) + [1] * (v + 1)
    cells += U.group(U.END)
    return cells


def verdict(seq, cand, steps=200000):
    tm, _ = U.build(5)
    cells = tape_for(seq, cand)
    tape = dict(enumerate(cells))
    pos, st, n = len(cells) - 5, 'P1#p', 0
    while n < steps:
        b = tape.get(pos, 0)
        if (st, b) not in tm.tr:
            return 'halt:' + st, n
        if st.startswith('H#'):
            # one shared read-back: at H#k the marker's top bit *is* the verdict
            return ('LEGAL' if b else 'ILLEGAL'), n
        w, mv, nx = tm.tr[(st, b)]
        tape[pos] = w
        pos += 1 if mv == 'R' else -1
        st = nx
        n += 1
    return 'TIMEOUT ' + st, n


if __name__ == '__main__':
    cases = [
        ([0], 0, 'LEGAL'),
        ([0, 0], 0, 'ILLEGAL'),
        ([0, 0], 1, 'LEGAL'),
        ([0, 0, 1], 0, 'ILLEGAL'),
        ([0, 0, 1], 1, 'LEGAL'),
        ([0, 0, 1, 1], 0, 'LEGAL'),
        ([0, 0, 1, 1, 0, 0], 0, 'ILLEGAL'),
        ([0, 0, 1, 1, 0, 0], 1, 'ILLEGAL'),
        ([0, 0, 1, 1, 0, 0], 2, 'LEGAL'),
        ([0, 0, 1, 1, 0, 0, 2], 0, 'ILLEGAL'),
        ([0, 0, 1, 1, 0, 0, 2], 1, 'LEGAL'),
    ]
    for seq, cand, want in cases:
        got, n = verdict(seq, cand)
        print('%-28s + %d -> %-22s %-8s (%d steps)'
              % (seq, cand, got, 'OK' if got == want else 'WANT ' + want, n))
