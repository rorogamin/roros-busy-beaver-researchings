"""Tower scaffolding for omega^omega^omega: a chain of doubling levels with a
finite meter, so the machine HALTS after (rank omega^d) work.

Core (rocq/Core.v) layout:   0^inf [C] 0 [U] 0 [W] 0^inf
Each "level" is one whole core run: [C] and [U] are consumed, [W] grows.

Layout used here:

    [M = 1^d] 0 [C] 0 [U] 0 [W]

M is the meter: it loses one cell per level.  When it runs out the machine halts.
At every level end the machine does two things:

  1. meter step (states E0,E1): walk left over the blank old-C/old-U region to
     the meter's rightmost mark and erase it; if the cell to its left is blank
     the meter is empty, so halt;
  2. level advance (states L0..RC, the same eight states as rung omega^omega):
     walk right to the old output, write a fresh `0 1 0 1`, and hand back to the
     core with the output relabelled as the next level's counter.

Level k's counter is level k-1's output, so each level costs exponentially more
than the one before, and the meter runs level 1, 2, ..., d.  The run therefore
halts after a tower of height d: rank omega^d -- NOT omega^omega^omega.  What is
missing for the tetration rung is a way to refill the meter from the counter at
a tier boundary, and that needs a block copy (the meter and the counter would
have to be two blocks of the same size, and the core destroys whichever one it
is given).

Two symbols, 0 = blank and 1 = mark.
"""
import tm

C, U, W, D = 1, 1, 1, 2      # boot: [M = 1^D] 0 [C] 0 [U] 0 [W]; D=2 so the
                             # emitted machine's halt is measured, not argued


def build(d=D, c=C, u=U, w=W):
    """Table with state numbers computed from the boot size, so nothing collides."""
    t = {}
    pat = 'O' * d + 'Z' + 'O' * c + 'Z' + 'O' * u + 'Z' + 'O' * w
    n = len(pat)
    base = 15                     # 0..14 is the core
    b = base + n                  # first walk-back state
    W0 = b + 6                    # walk right over the meter
    W1 = W0 + 1                   # step over the gap, stop on C's leftmost
    E0, E1 = W1 + 1, W1 + 2       # meter step
    L0, L1, L2, L3, L4, RA, RB, RC = range(E1 + 1, E1 + 9)
    nstates = RC + 1

    # boot: state 0 on a blank jumps to the write chain
    t[(0, 0)] = (0, 'R', base)
    for i, ch in enumerate(pat):
        nxt = base + i + 1 if i + 1 < n else b
        t[(base + i, 0)] = (1 if ch == 'O' else 0, 'R', nxt)
    # walk-back: left over the whole pattern, then right to C's leftmost cell
    t[(b, 0)] = (0, 'L', b + 1)
    for j, (on_, bl_) in enumerate((('L', 'L'), ('L', 'L'), ('L', 'L'), ('L', 'L'), ('L', 'R'))):
        s = b + 1 + j
        nxt = s + 1 if j < 4 else W0
        t[(s, 1)] = (1, on_, nxt)
        t[(s, 0)] = (0, bl_, nxt)
    t[(W0, 1)] = (1, 'R', W0)
    t[(W0, 0)] = (0, 'R', W1)
    t[(W1, 0)] = (0, 'R', W1)
    t[(W1, 1)] = (1, 'R', 13)     # C's leftmost: enter the core's N0 sweep

    # the core, then the level-end path
    import mk_machines as mk
    t.update(mk.core_table())
    t[(12, 0)] = (0, 'L', E0)      # T2 on a blank: the counter is exhausted
    t[(E0, 0)] = (0, 'L', E0)      # cross the blank region to the meter
    t[(E0, 1)] = (0, 'L', E1)      # erase the meter's rightmost cell
    t[(E1, 1)] = (1, 'R', L0)      # meter still has cells: next level
    # (E1, 0) is undefined: the meter is empty, so halt

    t[(L0, 0)] = (0, 'R', L0)      # to the old output's leftmost mark
    t[(L0, 1)] = (1, 'R', L1)
    t[(L1, 1)] = (1, 'R', L1)      # over the output
    t[(L1, 0)] = (0, 'R', L2)
    t[(L2, 0)] = (1, 'R', L3)      # fresh [U]
    t[(L3, 0)] = (0, 'R', L4)      # the mandatory gap
    t[(L4, 0)] = (1, 'R', RA)      # fresh [W]
    t[(RA, 1)] = (1, 'L', RA)
    t[(RA, 0)] = (0, 'L', RB)
    t[(RB, 1)] = (1, 'L', RA)
    t[(RB, 0)] = (0, 'R', RC)      # two blanks: the left region
    t[(RC, 0)] = (0, 'R', 13)      # onto the new counter's leftmost cell
    return t, nstates


def rle(tape, head):
    ks = [k for k, v in tape.items() if v] + [head]
    lo, hi = min(ks) - 1, max(ks) + 1
    out, i = [], lo
    while i <= hi:
        v = tape.get(i, 0)
        j = i
        while j + 1 <= hi and tape.get(j + 1, 0) == v:
            j += 1
        out.append(str(v) + (f'^{j - i + 1}' if j > i else ''))
        i = j + 1
    return ' '.join(out)


def run(d=D, steps=3000000):
    t, ns = build(d=d)
    m = tm.TM(ns, t)
    tape, head, state = {}, 0, 0
    levels, ran = [], 0
    for i in range(1, steps + 1):
        if state == 12 and tape.get(head, 0) == 0:
            levels.append(i)
        r = m.step(tape, head, state)
        if r is None:
            return dict(d=d, states=ns, halted=True, steps=i, levels=levels,
                        tape=tape, head=head, state=state)
        head, state = r
        ran = i
    return dict(d=d, states=ns, halted=False, steps=ran, levels=levels,
                tape=tape, head=head, state=state)


if __name__ == '__main__':
    print('tower scaffolding: halts after d levels, rank omega^d')
    for d in (1, 2, 3, 4):
        r = run(d=d)
        print('  d=%d: %2d states | halted %-5s %9d steps | level ends at %s'
              % (d, r['states'], r['halted'], r['steps'], r['levels'][:6]))
    r = run(d=3)
    print('  final tape for d=3:', rle(r['tape'], r['head']))
    t, ns = build(d=2)
    lines = ['# rung_omega_3lvl: TWO symbols; meter of d cells, one per level, then halt',
             '# core = proved 15-state doubling core; meter step E0/E1; level advance L0..RC',
             '# layout [M = 1^d] 0 [C] 0 [U] 0 [W]; d=2 here (measured halting); rank omega^d',
             '# format: <state> <read> <write> <dir> <next>;  a missing pair means halt']
    import mk_machines as mk
    lines.append(mk.to_text(t, ns).rstrip())
    open('machines/rung_omega_3lvl.txt', 'w').write('\n'.join(lines) + '\n')
    print('emitted machines/rung_omega_3lvl.txt')
