"""Compact snapshots of the 15-state candidate: output block and field lengths.

Run: python tools/_decode15_snap.py
"""

import sys

sys.path.insert(0, 'tools')

import tm

CAPS = [100, 1_000, 10_000, 100_000, 1_000_000, 2_000_000, 5_000_000,
        10_000_000, 50_000_000]


def runs(tape):
    ks = list(tape.keys())
    lo, hi = min(ks) - 1, max(ks) + 1
    out, i = [], lo
    while i <= hi:
        v = tape.get(i, 0)
        j = i
        while j + 1 <= hi and tape.get(j + 1, 0) == v:
            j += 1
        out.append((v, j - i + 1))
        i = j + 1
    return out


def main():
    m = tm.load('machines/candidate_15_omega2.txt')
    for cap in CAPS:
        steps, tape, head, state, halted = m.run(max_steps=cap)
        rr = runs(tape)
        ones = [n for v, n in rr if v == 1]
        zeros = [n for v, n in rr if v == 0]
        print(f'cap={cap:>11,} steps={steps:>11,} halt={halted} state={state} '
              f'head={head:>7} ones={sum(ones):>6}')
        print(f'  output={ones[0] if ones else 0} '
              f'fields={ones[1:]}')
        print(f'  zero_gaps={zeros}')


if __name__ == '__main__':
    main()
