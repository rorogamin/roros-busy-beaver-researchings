"""Rung omega^omega on TWO symbols: an unbounded chain of doubling levels.

Core layout (rocq/Core.v):

    0^inf  [C]  0  [U]  0  [W]  0^inf

The core erases one cell of [C] per macro pass, consumes all of [U], appends two
cells to [W], and halts when [C] is exhausted, leaving a single block behind.

For omega^omega the halt becomes a level advance.  No copy primitive is needed:
the core destroys its counter anyway, so the previous level's output block simply
becomes the next level's counter, and a fresh one-cell fuel and one-cell output
are written to its right.  The new layout is again

    [C = old output]  0  [U = 1]  0  [W = 1]

Eight states do it:

    26 L0  walk right over the blank region to the old output's leftmost mark
    27 L1  walk right over the old output to its right end
    28 L2  write the new fuel cell [U] = 1
    29 L3  step over the gap cell that must separate [U] from [W]
    30 L4  write the new output cell [W] = 1
    31 RA  return walk: over marks left; on a blank, step left and test
    32 RB  on a mark: keep walking left; on a blank: two blanks in a row, so the
           left region has been reached
    33 RC  one more step right, onto the new counter's leftmost cell, then enter
           the core's N0 sweep

Measured levels of the emitted machine (level k's counter is level k-1's output):

    level 1: counter 1  ->  level ends at step 28  with 3 marks
    level 2: counter 3  ->  level ends at step 276 with 12 marks
    level 3: counter 12 ->  still running after 3 000 000 steps

so the level runtimes are 28, 248, > 1e7: each level costs exponentially more
than the one before, and the chain of levels is unbounded.  That is rank
omega^omega.

State count: 15 core + 5 boot writes + 6 boot walk-back + 8 advance = 34.
The boot is pinned at C = U = W = 1; a larger boot would need more write states
and would collide with the advance states at 26..33.
"""
import mk_machines as mk
import tm

L0, L1, L2, L3, L4, RA, RB, RC = range(26, 34)
NSTATES = 34


def build(c=1, u=1, w=1):
    bt, nxt = mk.boot_table(c, u, w)
    if nxt > L0:
        raise ValueError('boot with c=%d needs states up to %d, colliding with '
                         'the advance states at %d' % (c, nxt - 1, L0))
    t = dict(bt)
    t.update(mk.core_table())
    # T2 on a blank would halt: walk out and start the next level instead
    t[(12, 0)] = (0, 'R', L0)
    t[(L0, 0)] = (0, 'R', L0)
    t[(L0, 1)] = (1, 'R', L1)
    t[(L1, 1)] = (1, 'R', L1)
    t[(L1, 0)] = (0, 'R', L2)      # onto the gap cell right of the old output
    t[(L2, 0)] = (1, 'R', L3)      # new [U]
    t[(L3, 0)] = (0, 'R', L4)      # the mandatory gap
    t[(L4, 0)] = (1, 'R', RA)      # new [W]
    t[(RA, 1)] = (1, 'L', RA)
    t[(RA, 0)] = (0, 'L', RB)
    t[(RB, 1)] = (1, 'L', RA)
    t[(RB, 0)] = (0, 'R', RC)      # two blanks in a row: the left region
    t[(RC, 0)] = (0, 'R', 13)      # onto the new counter's leftmost cell
    return t, NSTATES


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


def run(c=1, steps=3000000):
    """Run the booted machine; record every level end (T2 meeting a blank)."""
    t, ns = build(c=c)
    m = tm.TM(ns, t)
    tape, head, state = {}, 0, 0
    levels, ran, halted = [], 0, False
    for i in range(1, steps + 1):
        if state == 12 and tape.get(head, 0) == 0:
            levels.append((i, sum(1 for v in tape.values() if v)))
        r = m.step(tape, head, state)
        if r is None:
            halted, ran = True, i
            break
        head, state = r
        ran = i
    return levels, halted, ran, tape, head, state


def run_tape(tape, head, state, steps):
    """Run a preloaded tape; return (level ends, halted, tape, head, state)."""
    t, ns = build()
    m = tm.TM(ns, t)
    tape = dict(tape)
    ends, halted = [], False
    for i in range(1, steps + 1):
        if state == 12 and tape.get(head, 0) == 0:
            ends.append((i, sum(1 for v in tape.values() if v)))
        r = m.step(tape, head, state)
        if r is None:
            halted = True
            break
        head, state = r
    return ends, halted, tape, head, state


def preload(m):
    """Tape for one core run: [C = 1^m] 0 [U = 1] 0 [W = 1], head on C's leftmost."""
    tape = {i: 1 for i in range(1, m + 1)}
    tape[m + 2] = 1
    tape[m + 4] = 1
    return tape


def advance_test(m, settle=120, steps=2000000):
    """Run one level on a preloaded counter of size m, then stop shortly after
    the level advance so the new counter can be read off the tape."""
    t, ns = build()
    m_ = tm.TM(ns, t)
    tape, head, state = preload(m), 1, 13
    ends = []
    for i in range(1, steps + 1):
        if state == 12 and tape.get(head, 0) == 0:
            ends.append((i, sum(1 for v in tape.values() if v)))
            for _j in range(settle):
                r = m_.step(tape, head, state)
                if r is None:
                    return dict(m=m, ends=ends, halted=True, new_c=-1, head=head, tape=tape)
                head, state = r
            marks = sum(1 for v in tape.values() if v)
            return dict(m=m, ends=ends, halted=False, new_c=marks - 2,
                        head=head, tape=tape)
        r = m_.step(tape, head, state)
        if r is None:
            return dict(m=m, ends=ends, halted=True, new_c=-1, head=head, tape=tape)
        head, state = r
    return dict(m=m, ends=ends, halted=False, new_c=-1, head=head, tape=tape)


def layout_test(m=None, steps=2000000):
    """After the advance hands back to the core, is the tape [C] 0 [U] 0 [W]?"""
    t, ns = build()
    mach = tm.TM(ns, t)
    if m is None:
        tape, head, state = {}, 0, 0
    else:
        tape, head, state = preload(m), 1, 13
    ended = False
    for i in range(1, steps + 1):
        if state == 12 and tape.get(head, 0) == 0:
            ended = True
        r = mach.step(tape, head, state)
        if r is None:
            return dict(ok=False, why='halted at %d' % i, step=i)
        head, state = r
        if ended and state == 13:
            marks = sum(1 for v in tape.values() if v)
            return dict(ok=True, step=i, tape=rle(tape, head), c=marks - 2)
    return dict(ok=False, why='no advance in %d steps' % steps, step=steps)


if __name__ == '__main__':
    print('=== omega^omega: 34 states, 2 symbols ===')
    levels, halted, ran, tape, head, state = run(c=1, steps=3000000)
    print('levels in 3 000 000 steps (step, marks):', levels)
    print('halted:', halted, '| marks at the end:',
          sum(1 for v in tape.values() if v))

    print('--- layout right after the advance (expect 1^C 0 1 0 1) ---')
    lay_ok = True
    for m, expect in ((None, 3), (1, 3), (2, 6), (3, 12)):
        r = layout_test(m)
        good = bool(r['ok']) and r['c'] == expect and r['tape'].endswith('0 1 0 1 0')
        lay_ok = lay_ok and good
        print('  %-9s -> %s  C=%s (expect %s) %s'
              % ('booted' if m is None else 'counter %d' % m, r.get('tape'),
                 r.get('c'), expect, 'OK' if good else 'WRONG'))

    ok = (not halted) and len(levels) >= 2 and lay_ok
    table, nstates = build()
    lines = ['# rung_omega_omega: TWO symbols; each level becomes the next counter',
             '# core = proved 15-state doubling core, halt replaced by a level advance',
             '# (8 advance states); boot writes 1^C 0 1^U 0 1^W with C=U=W=1; 34 states',
             '# format: <state> <read> <write> <dir> <next>;  a missing pair means halt']
    lines.append(mk.to_text(table, nstates).rstrip())
    open('machines/rung_omega_omega.txt', 'w').write('\n'.join(lines) + '\n')
    print('emitted machines/rung_omega_omega.txt')
    print('CHECK', 'PASS' if ok else 'FAIL')
