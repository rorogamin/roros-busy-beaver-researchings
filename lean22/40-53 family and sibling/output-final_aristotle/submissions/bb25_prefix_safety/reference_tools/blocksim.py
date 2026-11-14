"""Block-level ("longitudinal") simulator for the whole family
1RB2LA0RB1LB---_1LA3RA1RA4LB---, for all 13 choices of B4.

Left blocks (nearest to the head first):
  L=^11  W=03  X=11  Z=01  J=023  J1=013  J0=003  K0=001  K1=011
Right blocks (nearest to the head first):
  R=$  R1=1$  R2=2$  U=12  V=21  X=11  Y=22  F=141  G=241  P1=1  P2=2
  N1=101  N2=201
States: 'R' = A>, 'L' = <A, 'B' = <B1 (a left-facing B head followed by a 1).

Every rule below is one of the rules verified in the Lean development.
"""
import sys
from sim import machine, step as basestep, A, B

LDEN = {'L': [1, 1], 'W': [3, 0], 'X': [1, 1], 'Z': [1, 0], 'J': [3, 2, 0],
        'J1': [3, 1, 0], 'J0': [3, 0, 0], 'K0': [1, 0, 0], 'K1': [1, 1, 0]}
RDEN = {'R': [], 'R1': [1], 'R2': [2], 'U': [1, 2], 'V': [2, 1], 'X': [1, 1],
        'Y': [2, 2], 'F': [1, 4, 1], 'G': [2, 4, 1], 'P1': [1], 'P2': [2],
        'N1': [1, 0, 1], 'N2': [2, 0, 1]}

# digit shifts (0 base steps): pure re-parsings of the tape
SHIFT1 = {'R': ['R1'], 'R1': ['X', 'R'], 'R2': ['U', 'R'], 'X': ['X', 'P1'],
          'V': ['U', 'P1'], 'Y': ['U', 'P2'], 'U': ['X', 'P2'], 'P1': ['X'],
          'P2': ['U']}
SHIFT2 = {'R': ['R2'], 'R1': ['V', 'R'], 'R2': ['Y', 'R'], 'X': ['V', 'P1'],
          'V': ['Y', 'P1'], 'Y': ['Y', 'P2'], 'U': ['V', 'P2'], 'P1': ['V'],
          'P2': ['Y']}

# A> 241 for each member: (new state, left blocks pushed, right blocks, steps)
GRULE = {
    '2LB': ('L', [], ['U', 'P1'], 3),
    '2RB': ('R', ['J'], [], 3),
    '1LB': ('L', [], ['X', 'P1'], 3),
    '1RB': ('R', ['J1'], [], 3),
    '0LB': ('L', [], ['N1'], 3),
    '0RB': ('R', ['J0'], [], 3),
    '3RA': ('L', [], ['X', 'P2'], 5),
    '2LA': ('L', [], ['Y', 'P2'], 7),
    '2RA': ('R', ['K0'], [], 5),
    '1LA': ('B', [], ['Y'], 9),
    '1RA': ('R', ['X'], ['P2'], 6),
    '0LA': ('L', [], ['V', 'P1'], 5),
    '0RA': ('R', ['K1'], [], 5),
}


class Stuck(Exception):
    pass


def bstep(member, lt, st, rt):
    """One block step. Returns (lt, st, rt, base_steps)."""
    if st == 'R':
        if rt and rt[0] in ('P1', 'P2'):
            tbl = SHIFT1 if rt[0] == 'P1' else SHIFT2
            if len(rt) == 1:
                return lt, 'R', ['R1' if rt[0] == 'P1' else 'R2'], 0
            nxt = rt[1]
            if rt[0] == 'P1' and nxt in ('F', 'G'):
                # A> 1> 141 -> <A 2> 141 (one base step); harmless in itself
                return lt, 'L', ['P2', nxt] + rt[2:], 1
            if nxt not in tbl:
                raise Stuck(f'digit {rt[0]} meets {nxt}')
            return lt, 'R', tbl[nxt] + rt[2:], 0
        if not rt or rt == ['R']:
            return lt, 'L', ['V', 'R'], 3
        if rt == ['R1']:
            return lt, 'L', ['R2'], 1
        if rt == ['R2']:
            return lt, 'B', ['Y', 'R1'], 11
        b, rest = rt[0], rt[1:]
        if b == 'X':
            return lt, 'L', ['V'] + rest, 1
        if b == 'V':
            return ['W'] + lt, 'R', rest, 2
        if b == 'Y':
            return ['Z'] + lt, 'R', rest, 2
        if b == 'U':
            return lt, 'L', ['Y'] + rest, 1
        if b == 'F':
            return lt, 'L', ['G'] + rest, 1
        if b == 'N1':
            return lt, 'L', ['N2'] + rest, 1
        if b == 'N2':
            return lt, 'B', ['Y'] + rest, 9
        if b == 'G':
            st2, push, emit, k = GRULE[member]
            return push + lt, st2, emit + rest, k
        raise Stuck(f'A> {b}')
    if st == 'L':
        if lt == ['L']:
            return lt, 'R', ['P2'] + rt, 4
        if not lt:
            raise Stuck('<A at the blank left region')
        b, rest = lt[0], lt[1:]
        if b == 'W':
            return rest, 'L', ['X'] + rt, 2
        if b == 'Z':
            return ['X'] + rest, 'R', rt, 3
        if b == 'X':
            return rest, 'L', ['Y'] + rt, 2
        if b == 'J':
            return ['X'] + rest, 'R', ['P2'] + rt, 6
        if b == 'J1':
            return rest, 'L', ['X', 'P2'] + rt, 5
        if b == 'J0':
            return rest, 'B', ['Y'] + rt, 9
        if b == 'K0':
            return ['K1'] + rest, 'R', rt, 3
        if b == 'K1':
            return ['X'] + rest, 'R', ['P2'] + rt, 4
        raise Stuck(f'{b} <A')
    if st == 'B':
        if not lt or lt == ['L']:
            raise Stuck('<B1 reaches the left end (left spinout: never halts)')
        b, rest = lt[0], lt[1:]
        if b == 'W':
            return rest, 'L', ['F'] + rt, 2
        if b == 'Z':
            return rest, 'L', ['X', 'P2'] + rt, 4
        if b == 'X':
            return rest, 'B', ['Y'] + rt, 6
        raise Stuck(f'{b} <B1')
    raise Stuck('bad state')


def stride(lt):
    """Accelerated left stride for state <A: only W/X/Z blocks."""
    n = 1
    counts = []
    for b in lt:
        counts.append(n)
        if b == 'W':
            n = 2 * n
        elif b == 'Z':
            n = n // 2
        elif b == 'X':
            n = n // 2 + n % 2
        else:
            return None
        if n == 0:
            break
    if n != 0:
        return None
    out = list(lt)
    k = 0
    for i, c in enumerate(counts):
        b = out[i]
        if b == 'W':
            k += 5 * c
        elif b == 'X':
            k += 7 * (c // 2) + (4 if c % 2 else 0)
            if c % 2:
                out[i] = 'Z'
        elif b == 'Z':
            k += 7 * (c // 2) + (3 if c % 2 else 0)
            if c % 2:
                out[i] = 'X'
    return out, k


def denote(lt, st, rt):
    l = []
    for b in lt:
        l += LDEN[b]
    r = []
    for b in rt:
        r += RDEN[b]
    if st == 'R':
        return (l, A, 'R', r)
    if st == 'L':
        return (l, A, 'L', r)
    return (l, B, 'L', [1] + r)


def run(member, nsteps, use_stride=True, check=0, verbose=0):
    lt, st, rt = ['L'], 'R', ['R1']
    total = 5  # the initial 5 steps reaching ^11 A> 1$
    m = machine(None)
    for i in range(nsteps):
        if check and i < check:
            # cross-check the block state against the real machine
            c = (list(reversed([])), )  # placeholder
        if use_stride and st == 'L':
            s = stride(lt)
            if s is not None:
                lt, k = s
                st = 'R'
                total += k
                continue
        try:
            lt, st, rt, k = bstep(member, lt, st, rt)
        except Stuck as e:
            return i, total, f'STUCK: {e}', (lt, st, rt)
        total += k
    return nsteps, total, 'ok', (lt, st, rt)


def crosscheck(member, nsteps):
    """Verify the block simulation against the base machine, step by step."""
    m = machine(machineB4(member))
    lt, st, rt = ['L'], 'R', ['R1']
    c = denote(lt, st, rt)
    for i in range(nsteps):
        try:
            lt2, st2, rt2, k = bstep(member, lt, st, rt)
        except Stuck as e:
            return f'stuck after {i}: {e}'
        for _ in range(k):
            c = basestep(m, c)
            if c is None:
                return f'base machine halted inside block step {i}'
        if c != denote(lt2, st2, rt2):
            return (f'MISMATCH at block step {i}: {(lt,st,rt)} -> {(lt2,st2,rt2)}\n'
                    f'  base {c}\n  pred {denote(lt2,st2,rt2)}')
        lt, st, rt = lt2, st2, rt2
    return 'ok'


def machineB4(name):
    sym = int(name[0])
    d = name[1]
    q = A if name[2] == 'A' else B
    return (sym, d, q)


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    print('=== cross-check of the block rules against the base machine ===')
    for member in GRULE:
        print(f'{member}: {crosscheck(member, min(n, 4000))}')
    print()
    print(f'=== block simulation, {n} steps (with left strides) ===')
    for member in GRULE:
        i, total, status, (lt, st, rt) = run(member, n)
        print(f'{member}: block steps {i}, base steps ~10^{len(str(total))-1} '
              f'({total if total < 10**12 else str(total)[:6] + "..."}), {status}, '
              f'|left|={len(lt)} |right|={len(rt)}')
