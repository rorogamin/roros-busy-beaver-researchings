"""Verify the decoded H..O instruction semantics on synthetic tapes.

Rules under test:
  H on 1 -> 0 R O; O on 1 -> 1 R M; O on 0 -> halt.
  triple M/N/O on 1: `1 1 1` -> `0 1 1`, head +3, back to M.
  entry  H on `1^(3k+2)`: `0 1 (011)^k`, head at 3k+2, state M.
  forty  H on `1^40`: the 40 cells become the 13-token boundary form.

Run: python tools/_decode15_semantics.py
"""

import sys

sys.path.insert(0, 'tools')

import tm

NAMES = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F', 6: 'G',
         7: 'H', 8: 'I', 9: 'J', 10: 'K', 11: 'L', 12: 'M', 13: 'N',
         14: 'O'}


def sname(s):
    return 'HALT' if s is None else NAMES[s]


def bits(tape, lo, hi):
    return ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def run(m, tape, head, state, steps):
    for i in range(steps):
        t = m.t.get((state, tape.get(head, 0)))
        if t is None:
            return head, state, True, i
        tape[head] = t[0]
        head += 1 if t[1] == 'R' else -1
        state = t[2]
        if state is None:
            return head, None, True, i + 1
    return head, state, False, steps


def show(m, label):
    print(label)
    for b in (0, 1):
        t = m.t.get((7, b))  # placeholder to keep the table order
        break
    for s in (7, 14, 12, 13):
        for b in (0, 1):
            t = m.t.get((s, b))
            if t is None or t[2] is None:
                print(f'  {NAMES[s]} ({s}) on {b} -> HALT')
            else:
                w, d, nxt = t
                print(f'  {NAMES[s]} ({s}) on {b} -> {w} {d} {NAMES[nxt]}')


def main():
    m = tm.load('machines/candidate_15_omega2.txt')
    show(m, 'H..O transitions:')
    print('neighbours:')
    for s in (0, 6, 5):
        for b in (0, 1):
            t = m.t.get((s, b))
            if t is None or t[2] is None:
                print(f'  {NAMES[s]} ({s}) on {b} -> HALT')
            else:
                w, d, nxt = t
                print(f'  {NAMES[s]} ({s}) on {b} -> {w} {d} {NAMES[nxt]}')

    print('\nsingle 1 at H:')
    tape = {0: 1}
    h, s, halt, n = run(m, tape, 0, 7, 2)
    print(f'  after {n} steps: head={h} state={sname(s)} halt={halt} '
          f'bits={bits(tape, 0, 1)}')

    print('\ntriple 111 -> 011:')
    tape = {0: 1, 1: 1, 2: 1}
    h, s, halt, n = run(m, tape, 0, 12, 3)
    print(f'  after {n} steps: head={h} state={sname(s)} bits={bits(tape, 0, 2)} '
          f'halt={halt}  ' + ('OK' if (bits(tape, 0, 2) == '011' and h == 3
                                       and s == 12 and not halt) else 'BAD'))

    print('\nwriter 1^3k -> (011)^k (start M):')
    for k in (1, 2, 3, 13):
        tape = {i: 1 for i in range(3 * k)}
        h, s, halt, n = run(m, tape, 0, 12, 3 * k)
        want = '011' * k
        got = bits(tape, 0, 3 * k - 1)
        print(f'  k={k:>2}: after {n} head={h} state={sname(s)} '
              f'{got == want}')

    print('\nentry H on 1^(3k+2) -> 01(011)^k (start H):')
    for k in (1, 2, 3, 12):
        tape = {i: 1 for i in range(3 * k + 2)}
        h, s, halt, n = run(m, tape, 0, 7, 3 * k + 2)
        want = '01' + '011' * k
        got = bits(tape, 0, 3 * k + 1)
        print(f'  k={k:>2}: after {n} head={h} state={sname(s)} halt={halt} '
              f'{got == want}  {got}')

    print('\nforty 1^40 (start H, 60 steps):')
    tape = {i: 1 for i in range(40)}
    h, s, halt, n = run(m, tape, 0, 7, 60)
    print(f'  after {n} steps: head={h} state={sname(s)} halt={halt}')
    print(f'  bits 0..45: {bits(tape, 0, 45)}')
    print(f'  first 39:   {bits(tape, 0, 38)}')
    print(f'  tail 35..45:{bits(tape, 35, 45)}')


if __name__ == '__main__':
    main()
