"""Dump the 15-state candidate's tape layout and trace its suffix logic.

Run: python tools/_decode15_dump.py [step]
"""

import sys

sys.path.insert(0, 'tools')

import tm


def run_rle(tape, head):
    ks = [k for k, v in tape.items() if v] + [head]
    lo, hi = min(ks) - 1, max(ks) + 1
    out, i = [], lo
    while i <= hi:
        v = tape.get(i, 0)
        j = i
        while j + 1 <= hi and tape.get(j + 1, 0) == v:
            j += 1
        out.append((i, j, v))
        i = j + 1
    return out


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
    m = tm.load('machines/candidate_15_omega2.txt')
    steps, tape, head, state, halted = m.run(max_steps=cap)
    print(f'steps={steps:,} halted={halted} state={state} head={head} '
          f'score={m.score(tape)}')
    rr = run_rle(tape, head)
    print('runs:')
    for a, b, v in rr:
        print(f'  [{a},{b}] {v}^{b - a + 1}')
    blocks = [(a, b) for a, b, v in rr if v == 1]
    a, b = max(blocks, key=lambda t: t[1] - t[0])
    print(f'block [{a},{b}] len={b - a + 1}')
    hi = max(k for k, v in tape.items() if v)
    print('suffix = ' + ''.join(str(tape.get(i, 0)) for i in range(b + 1, hi + 1)))
    print('suffix ones = ' + str(sum(1 for i in range(b + 1, hi + 1) if tape.get(i, 0))))

    log = []
    n = 0
    start = (head, state)
    while n < 200_000:
        read = tape.get(head, 0)
        r = m.step(tape, head, state)
        if r is None:
            print(f'HALT at {steps + n + 1}')
            break
        w, d, nxt = m.t[(state, read)]
        n += 1
        if head > b:
            log.append((n, state, head, read, w, d, nxt))
        head, state = r
        if log and head <= b and state < 7:
            break
    print(f'trace start={start} entries={len(log)} '
          f'after: state={state} head={head}')
    for e in log[:500]:
        print('  t=%d s=%d h=%d r=%d -> w=%d %s %d' % e)


if __name__ == '__main__':
    main()
