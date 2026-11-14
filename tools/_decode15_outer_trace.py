"""Trace the H..O writer's entry and boundary in the 15-state candidate.

At ~6M steps the unary `1^out 0 1^fuel` region merges and the M/N/O states
rewrite it as `0 1 1` triples (the `11 0` token chain).  This probe starts
just before that merge, logs every H..O step with a local window, and checks
each M/N/O triple against the rule `111 -> 011` moving right by 3.

Run: python tools/_decode15_outer_trace.py [base] [cap]
"""

import sys

sys.path.insert(0, 'tools')

import tm

H_STATES = (7, 14, 12, 13)


def ones_runs(tape):
    ks = sorted(k for k, v in tape.items() if v)
    runs = []
    if not ks:
        return runs
    start = prev = ks[0]
    for k in ks[1:]:
        if k == prev + 1:
            prev = k
        else:
            runs.append((start, prev))
            start = prev = k
    runs.append((start, prev))
    return runs


def window(tape, head, back=6, fwd=8):
    lo, hi = head - back, head + fwd
    return ''.join('<' + str(tape.get(i, 0)) + '>' if i == head
                   else str(tape.get(i, 0)) for i in range(lo, hi + 1))


def main():
    base = int(sys.argv[1]) if len(sys.argv) > 1 else 5_995_000
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 20_000
    keep = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    m = tm.load('machines/candidate_15_omega2.txt')
    steps, tape, head, state, halted = m.run(max_steps=base)
    tape = dict(tape)
    runs = ones_runs(tape)
    lstart, lend = runs[2]
    for i in range(lstart + keep, lend + 1):
        tape.pop(i, None)
    print(f'base={base:,} state={state} head={head} halt={halted} '
          f'level {lend - lstart + 1}->{keep}')

    entries = []
    triples = []
    last = None
    for i in range(1, cap + 1):
        read = tape.get(head, 0)
        t = m.t.get((state, read))
        if t is None:
            print(f'HALT at {base + i}')
            break
        if state in H_STATES:
            w, d, nxt = t
            entries.append((base + i, state, head, read, w, d, nxt,
                            window(tape, head)))
            # A triple starts at M on 1 and continues N,O.
            if state == 12 and read == 1:
                if last is not None and last[0] != 13:
                    triples.append((base + i, head, 'start'))
        tape[head] = t[0]
        head += 1 if t[1] == 'R' else -1
        state = t[2]
        last = (state,)

    print(f'H..O entries in window: {len(entries)}')
    print('\nfirst 30 H..O entries:')
    for e in entries[:30]:
        print('  t=%d s=%d h=%d r=%d -> w%d %s %d  %s' % e)
    print('\nlast 30 H..O entries:')
    for e in entries[-30:]:
        print('  t=%d s=%d h=%d r=%d -> w%d %s %d  %s' % e)

    # Reconstruct the writer phase: consecutive M,N,O triples on 1s.
    runs = 0
    i = 0
    while i + 2 < len(entries):
        a, b, c = entries[i], entries[i + 1], entries[i + 2]
        if (a[1], a[3], a[4]) == (12, 1, 0) and \
           (b[1], b[3], b[4]) == (13, 1, 1) and \
           (c[1], c[3], c[4]) == (14, 1, 1) and \
           b[2] == a[2] + 1 and c[2] == a[2] + 2:
            runs += 1
        i += 1
    print(f'\nM/N/O 111->011 triple candidates: {runs}')


if __name__ == '__main__':
    main()
