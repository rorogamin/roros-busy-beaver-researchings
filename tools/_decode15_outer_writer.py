"""Trace the H..O writer on the level-1 tape from its actual entry.

Reproduces the `_decode15_outer.py` setup (run to 2M, shorten the third
1-run to one cell), advances to 8,000,000 steps, then logs every H..O step
for 20,000 steps.  Checks each M/N/O triple against `111 -> 011` and prints
the entry window, the triple count, and the last boundary window.

Run: python tools/_decode15_outer_writer.py [base] [advance] [cap]
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


def window(tape, head, back=5, fwd=7):
    return ''.join('<' + str(tape.get(i, 0)) + '>' if i == head
                   else str(tape.get(i, 0)) for i in range(head - back,
                                                           head + fwd + 1))


def main():
    base = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
    advance = int(sys.argv[2]) if len(sys.argv) > 2 else 6_000_000
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 20_000
    m = tm.load('machines/candidate_15_omega2.txt')
    steps, tape, head, state, halted = m.run(max_steps=base)
    tape = dict(tape)
    runs = ones_runs(tape)
    lstart, lend = runs[2]
    for i in range(lstart + 1, lend + 1):
        tape.pop(i, None)
    print(f'base={base:,} shorten [{lstart},{lend}] -> 1, '
          f'advance={advance:,}')

    # Advance to the writer entry.
    for _ in range(advance):
        t = m.t.get((state, tape.get(head, 0)))
        if t is None:
            print('halted during advance')
            return
        tape[head] = t[0]
        head += 1 if t[1] == 'R' else -1
        state = t[2]
    print(f'advance done: state={state} head={head} '
          f'runs={len(ones_runs(tape))}')

    entries = []
    triples = 0
    triple_bad = []
    for i in range(1, cap + 1):
        read = tape.get(head, 0)
        t = m.t.get((state, read))
        if t is None:
            print(f'HALT at advance+{i}')
            break
        if state in H_STATES:
            w, d, nxt = t
            entries.append((advance + i, state, head, read, w, d, nxt,
                            window(tape, head)))
        tape[head] = t[0]
        head += 1 if t[1] == 'R' else -1
        state = t[2]

    print(f'H..O entries in window: {len(entries)}')
    print('\nfirst 40 entries:')
    for e in entries[:40]:
        print('  t=%d s=%d h=%d r=%d -> w%d %s %d  %s' % e)
    print('\nlast 40 entries:')
    for e in entries[-40:]:
        print('  t=%d s=%d h=%d r=%d -> w%d %s %d  %s' % e)

    # Triple check: consecutive H..O entries M(1), N(1), O(1) at h, h+1, h+2.
    for i in range(len(entries) - 2):
        a, b, c = entries[i], entries[i + 1], entries[i + 2]
        if a[1] == 12 and a[3] == 1:
            ok = (b[1], b[3], b[4]) == (13, 1, 1) and \
                 (c[1], c[3], c[4]) == (14, 1, 1) and \
                 b[2] == a[2] + 1 and c[2] == a[2] + 2 and \
                 a[4] == 0
            triples += ok
            if not ok:
                triple_bad.append((a, b, c))
    print(f'\nM/N/O triples: {triples}, bad: {len(triple_bad)}')
    for a, b, c in triple_bad[:5]:
        print('  BAD', a, b, c)


if __name__ == '__main__':
    main()
