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


def halts_on_last(last, halt_on=5, steps=100000):
    """The halting claim itself, executed instead of assumed.

    Start at the dispatch -- the end marker's c0, where the verdict path hands
    over -- on a hand-built tape whose final record is `last`.  dispatch reads
    the last block back and halts iff its value is halt_on, so a 5 must reach
    HALT while 4 and 3 must go on to AP0x.  This is the one branch the
    blank-tape runs can never take (a 5 is never placed), which is why it has
    to be built by hand.
    """
    tm, _ = U.build(halt_on)
    cells = list(U.group(U.WALL)) + U.group(U.PLAIN)
    cells += [1] * (last + 1) + list(U.group(U.END))
    tape = dict(enumerate(cells))
    pos, st, n = len(cells) - 5, 'Hp#p', 0
    while n < steps:
        if st == 'HALT':                  # the halt label: no transitions
            return 'HALT', n
        if st == 'AP0x':                  # dispatch sent us round again
            return 'CONTINUE', n
        b = tape.get(pos, 0)
        if (st, b) not in tm.tr:
            return 'dead:' + st, n
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
    print()
    for last, want in ((5, 'HALT'), (4, 'CONTINUE'), (3, 'CONTINUE')):
        got, n = halts_on_last(last)
        print('dispatch, last record %d -> %-9s %-8s (%d steps)'
              % (last, got, 'OK' if got == want else 'WANT ' + want, n))
