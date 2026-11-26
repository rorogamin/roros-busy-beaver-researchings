"""Independent check of primes.py: run the machine and, on every round start,
decode the tape (blocks split on blanks) and compare the output blocks with
the primes below the candidate."""
import sys

import primes as P


def table():
    T = {}
    for line in P.machine().splitlines():
        st, rd, wr, mv, nx = line.split()
        T[(st, rd)] = (wr, {'l': -1, 'r': 1, '*': 0, 'n': 0}[mv], nx)
    return T


def blocks(tape):
    cells = sorted(p for p, s in tape.items() if s != '_')
    out, cur, prev = [], [], None
    for p in cells:
        if prev is not None and p != prev + 1:
            out.append(cur)
            cur = []
        cur.append(tape[p])
        prev = p
    if cur:
        out.append(cur)
    return [len(b) for b in out]


def primes_below(n):
    return [x for x in range(2, n) if all(x % d for d in range(2, int(x ** .5) + 1))]


def main(steps):
    T = table()
    tape, head, state, t = {}, 0, '0', 0
    prev = None
    rounds = 0
    top = 0
    print_at = 20
    while t < steps:
        if state == 'r0' and prev != 'r0':
            b = blocks(tape)
            n = b[0]
            got = b[1:]
            want = primes_below(n)
            if got != want:
                print('MISMATCH at step %d: C=%d output=%s expected=%s' % (t, n, got, want))
                return 1
            rounds += 1
            top = n
            if rounds >= print_at:
                print_at *= 2
                print('  step %8d  candidate %3d  output %s' % (t, n, got))
        prev = state
        rd = tape.get(head, '_')
        r = T.get((state, rd))
        if r is None:
            print('CRASH step %d state %s read %r head %d' % (t, state, rd, head))
            return 1
        wr, d, nx = r
        if wr == '_':
            tape.pop(head, None)
        else:
            tape[head] = wr
        head += d
        t += 1
        state = nx
    print('%d steps, %d rounds checked, candidate reached %d, all outputs correct'
          % (t, rounds, top))
    return 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 1000000))
