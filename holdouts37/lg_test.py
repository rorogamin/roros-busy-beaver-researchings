import sys, legendre as L


def table():
    T = {}
    for line in L.machine().splitlines():
        st, rd, wr, mv, nx = line.split()
        T[(st, rd)] = (wr, {'l': -1, 'r': 1, '*': 0, 'n': 0}[mv], nx)
    return T


def run(tape, steps=200000, trace_at=None, watch=None):
    T = table()
    head, state, t = 0, '0', 0
    hits = []
    while t < steps:
        rd = tape.get(head, '_')
        r = T.get((state, rd))
        if r is None:
            return ('crash', t, state, rd, head, hits)
        if watch and state == watch:
            hits.append((t, dump(tape)))
        wr, d, nx = r
        if wr == '_':
            tape.pop(head, None)
        else:
            tape[head] = wr
        head += d
        t += 1
        if nx == 'halt':
            return ('halt', t, state, wr, head, hits)
        state = nx
    return ('timeout', t, state, None, head, hits)


def dump(tape):
    lo = min([p for p, s in tape.items() if s == '^'], default=0)
    hi = max([p for p, s in tape.items() if s == ']'], default=0)
    return ''.join(tape.get(p, '_') for p in range(lo, hi + 1))


def boot(length=8, composites=()):
    s = L.start_tape(length, composites)
    hook = s.index('*') if '*' in s else None
    return {i: ch for i, ch in enumerate(s)}, 0


if __name__ == '__main__':
    tape, _ = boot(8)
    kind, t, st, sym, head, hits = run(tape, 60000, watch='q1')
    print(kind, 'step', t, 'state', st, 'sym', sym, 'head', head)
    if kind == 'crash':
        line = ''.join(tape.get(p, '_') for p in range(max(0, head - 30), head + 30))
        print('context:', line)
        print('tape   :', dump(tape)[:120])
    if hits:
        print('first check-phase tape:', hits[0][1][:100])
