"""Trace the 15-state candidate at the outer w*2 boundary.

The tape is `1^out 0 1^fuel 0 1^level 0 [13 fields] 0 1^40 0 ...`.
The first field of the pre-40 block is the level counter; each normal
level transition decrements it once.  To see what happens when it reaches
zero we run to a clean base step, shorten that field to a requested value,
and keep the rest of the numeral stack intact.  The head is far to the left
at the base step, so the edit is behind it.

Logs: every H..O (7,14,12,13) entry, every state when the head is in the
right-hand field region, and a run-length snapshot every 100k steps.  A
level-counter length change prints the last LOG transitions before it.

Run: python tools/_decode15_outer.py [level] [cap] [base]
"""

import sys

sys.path.insert(0, 'tools')

import tm

H_STATES = (7, 14, 12, 13)
LOG = 400


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


def layout(tape):
    runs = ones_runs(tape)
    return ' '.join(f'[{a},{b}]1^{b - a + 1}' for a, b in runs)


def shorten_run(tape, start, end, keep):
    """Keep the first `keep` cells of a 1-run; delete the rest."""
    for i in range(start + keep, end + 1):
        tape.pop(i, None)


def main():
    level = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 20_000_000
    base = int(sys.argv[3]) if len(sys.argv) > 3 else 2_000_000

    m = tm.load('machines/candidate_15_omega2.txt')
    steps, tape, head, state, halted = m.run(max_steps=base)
    tape = dict(tape)
    runs = ones_runs(tape)
    print(f'base={base:,} steps={steps:,} state={state} head={head} '
          f'halt={halted}')
    print(f'ones runs: {layout(tape)}')
    assert len(runs) >= 3, 'expected output, fuel, level runs'
    lstart, lend = runs[2]
    print(f'level field [{lstart},{lend}] len={lend - lstart + 1} '
          f'-> keep {level}')
    shorten_run(tape, lstart, lend, level)
    print(f'edited runs: {layout(tape)}')

    level_len = level
    hist = []
    last_snap = 0
    transitions = 0
    halted_at = None
    changed_at = None

    for i in range(1, cap + 1):
        read = tape.get(head, 0)
        t = m.t.get((state, read))
        # Record H..O always, and any state in the right-hand field region.
        if state in H_STATES or head > -300:
            if t is None:
                act = 'HALT'
            else:
                act = f'w{t[0]} {t[1]} {t[2]}'
            hist.append((i, state, head, read, act))
            if len(hist) > LOG:
                hist.pop(0)
        if t is None:
            halted_at = i
            break
        tape[head] = t[0]
        head += 1 if t[1] == 'R' else -1
        state = t[2]
        transitions = i

        if i - last_snap >= 100_000:
            last_snap = i
            print(f'  {i:>10,} state={state} head={head:>7} '
                  f'runs={layout(tape)}')
        # Watch the cell that held the level's first 1.
        cur = tape.get(lstart, 0)
        if level_len and cur == 0 and changed_at is None:
            changed_at = i
            print(f'\nlevel start cell blanked at step {i:,} state={state} '
                  f'head={head}')
            print(f'  runs: {layout(tape)}')
            print('last transitions:')
            for e in hist:
                print('  t=%d s=%d h=%d r=%d -> %s' % e)
            break

    print(f'\nran {transitions:,} steps, halt={halted_at}, '
          f'level_start_blanked={changed_at}')
    print(f'final state={state} head={head}')
    print(f'final runs: {layout(tape)}')


if __name__ == '__main__':
    main()
