"""Fast accelerated block simulator: left stack as list (top = end),
right stack as list (nearest the head = end).  Same rules as blocksim.py."""
import sys
from blocksim import GRULE, Stuck

SHIFT1 = {'R': ['R1'], 'R1': ['R', 'X'], 'R2': ['R', 'U'], 'X': ['P1', 'X'],
          'V': ['P1', 'U'], 'Y': ['P2', 'U'], 'U': ['P2', 'X'], 'P1': ['X'],
          'P2': ['U']}
SHIFT2 = {'R': ['R2'], 'R1': ['R', 'V'], 'R2': ['R', 'Y'], 'X': ['P1', 'V'],
          'V': ['P1', 'Y'], 'Y': ['P2', 'Y'], 'U': ['P2', 'V'], 'P1': ['V'],
          'P2': ['Y']}
# GRULE entries: (state, pushed left blocks [nearest first], right blocks [nearest first], steps)


def stride(lt):
    """Left stride for state <A.  lt is bottom-first; returns True if the head
    comes back out (n hits 0), mutating lt in place; False if it reaches the end."""
    n = 1
    i = len(lt) - 1
    while i >= 0:
        b = lt[i]
        if b == 'W':
            n = 2 * n
        elif b == 'X':
            n = (n + 1) // 2
        elif b == 'Z':
            n = n // 2
        else:
            return None
        i -= 1
        if n == 0:
            break
    if n != 0:
        return None
    # recompute with the parity information to rewrite the stack
    n = 1
    i = len(lt) - 1
    while i >= 0:
        b = lt[i]
        if b == 'W':
            n = 2 * n
        elif b == 'X':
            if n % 2:
                lt[i] = 'Z'
            n = (n + 1) // 2
        elif b == 'Z':
            if n % 2:
                lt[i] = 'X'
            n = n // 2
        i -= 1
        if n == 0:
            break
    return True


def run(member, nsteps, log=None):
    lt = ['L']            # bottom first; lt[-1] nearest the head
    rt = ['R1']           # farthest first; rt[-1] nearest the head
    st = 'R'
    grule = GRULE[member]
    for i in range(nsteps):
        if st == 'L':
            if stride(lt) is not None:
                st = 'R'
                continue
        if st == 'R':
            top = rt[-1]
            if top in ('P1', 'P2'):
                tbl = SHIFT1 if top == 'P1' else SHIFT2
                if len(rt) == 1:
                    rt[-1] = 'R1' if top == 'P1' else 'R2'
                    continue
                nxt = rt[-2]
                if top == 'P1' and nxt in ('F', 'G'):
                    rt[-1] = 'P2'
                    st = 'L'
                    continue
                if nxt not in tbl:
                    return i, f'DANGER: pending {top} meets {nxt}', lt, st, rt
                rt.pop(); rt.pop()
                rt.extend(tbl[nxt])
                continue
            if top == 'R':
                rt.pop(); rt.extend(['R', 'V']); st = 'L'; continue
            if top == 'R1':
                rt[-1] = 'R2'; st = 'L'; continue
            if top == 'R2':
                rt.pop(); rt.extend(['R1', 'Y']); st = 'B'; continue
            if top == 'X':
                rt[-1] = 'V'; st = 'L'; continue
            if top == 'V':
                rt.pop(); lt.append('W'); continue
            if top == 'Y':
                rt.pop(); lt.append('Z'); continue
            if top == 'U':
                rt[-1] = 'Y'; st = 'L'; continue
            if top == 'F':
                rt[-1] = 'G'; st = 'L'; continue
            if top == 'N1':
                rt[-1] = 'N2'; st = 'L'; continue
            if top == 'N2':
                rt[-1] = 'Y'; st = 'B'; continue
            if top == 'G':
                st2, push, emit, k = grule
                rt.pop()
                rt.extend(reversed(emit))
                lt.extend(reversed(push))
                st = st2
                continue
            return i, f'STUCK: A> {top}', lt, st, rt
        if st == 'L':
            b = lt[-1]
            if b == 'L':
                rt.append('P2'); st = 'R'; continue
            lt.pop()
            if b == 'W':
                rt.append('X'); continue
            if b == 'Z':
                lt.append('X'); st = 'R'; continue
            if b == 'X':
                rt.append('Y'); continue
            if b == 'J':
                lt.append('X'); rt.append('P2'); st = 'R'; continue
            if b == 'J1':
                rt.append('P2'); rt.append('X'); st = 'L'; continue
            if b == 'J0':
                rt.append('Y'); st = 'B'; continue
            if b == 'K0':
                lt.append('K1'); st = 'R'; continue
            if b == 'K1':
                lt.append('X'); rt.append('P2'); st = 'R'; continue
            return i, f'STUCK: {b} <A', lt, st, rt
        if st == 'B':
            b = lt[-1]
            if b == 'L':
                return i, 'SPINOUT: <B1 at the left end (never halts)', lt, st, rt
            lt.pop()
            if b == 'W':
                rt.append('F'); st = 'L'; continue
            if b == 'Z':
                rt.append('P2'); rt.append('X'); st = 'L'; continue
            if b == 'X':
                rt.append('Y'); continue
            return i, f'HALTS: {b} <B1', lt, st, rt
    return nsteps, 'ok', lt, st, rt


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    members = sys.argv[2:] or list(GRULE)
    for m in members:
        i, status, lt, st, rt = run(m, n)
        print(f'{m:4s} steps {i:8d} {status:20s} |L|={len(lt)} |R|={len(rt)}')
