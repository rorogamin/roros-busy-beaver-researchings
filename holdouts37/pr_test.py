import primes as P


def table():
    T = {}
    for line in P.machine().splitlines():
        st, rd, wr, mv, nx = line.split()
        T[(st, rd)] = (wr, {'l': -1, 'r': 1, '*': 0, 'n': 0}[mv], nx)
    return T


def blocks(tape):
    cells = sorted(p for p, s in tape.items() if s != '_')
    out, cur = [], []
    prev = None
    for p in cells:
        if prev is not None and p != prev + 1:
            out.append(cur)
            cur = []
        cur.append(tape[p])
        prev = p
    if cur:
        out.append(cur)
    return [len(b) for b in out]


def isprime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


T = table()
tape = {}
head, state, t = 0, '0', 0
rounds = 0
ok = True
while t < 400000:
    rd = tape.get(head, '_')
    if state == 'r0':
        b = blocks(tape)
        n = b[0]
        got = b[1:]
        want = [x for x in range(2, n) if isprime(x)]
        if got != want:
            print('round %d: C=%d output=%s expected=%s  MISMATCH' % (rounds, n, got[:12], want[:12]))
            ok = False
            break
        rounds += 1
        if rounds % 5 == 0:
            print('round %2d  step %7d  n=%2d  output=%s' % (rounds, t, n, got))
    r = T.get((state, rd))
    if r is None:
        lo, hi = head - 25, head + 25
        print('CRASH step %d state %s read %r head %d' % (t, state, rd, head))
        print('  around:', ''.join(tape.get(i, '_') for i in range(lo, hi)))
        print('  blocks:', blocks(tape)[:12])
        ok = False
        break
    wr, d, nx = r
    if wr == '_':
        tape.pop(head, None)
    else:
        tape[head] = wr
    head += d
    t += 1
    state = nx
else:
    print('still running at', t, state)

print('rounds completed', rounds, 'ok' if ok else 'FAILED')
