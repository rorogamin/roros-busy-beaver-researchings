"""Rung omega on TWO symbols, built by editing the proved 15-state core.

The core (rocq/Core.v, tools/mk_machines.py) has the layout

    0^inf  [C]  0  [U]  0  [W]  0^inf

and a pass erases one cell of [U], sweeps right over [U] and [W], appends two
cells to [W], sweeps back to [C], erases one cell of [C], and repeats.  It
halts when [C] runs out, because then there is nothing left to iterate.

Two single-transition edits remove the halt without adding a state:

    F1, blank : 0 -> 1   extend [U] by one cell at its right end
    T2, blank : 0 -> 1   put back the cell just erased from [C]

[U] loses one cell at its left end (A) and gains one at its right end (F1), so
its length is invariant and it never empties.  [C] loses one cell per macro
pass (A2) and the T2 edit writes it back whenever it reaches zero, so [C] never
empties either.  Nothing ever halts, and every pass appends two cells to [W]:
a genuine omega machine -- it runs for ever, with output that grows without
bound -- on two symbols.

State count: 15 core + 5 boot writes + 6 boot walk-back = 26.
"""
import mk_machines as mk
import tm

C, U, W = 1, 1, 1        # boot pattern 1^C 0 1^U 0 1^W


def build(c=C, u=U, w=W):
    """Core table with two edited transitions, plus the boot chain."""
    bt, nxt = mk.boot_table(c, u, w)
    t = dict(bt)
    t.update(mk.core_table())
    t[(3, 0)] = (1, 'R', 4)      # F1 on a blank: extend U
    t[(12, 0)] = (1, 'R', 13)    # T2 on a blank: refill C instead of halting
    return t, nxt


def marks(tape):
    return sum(1 for v in tape.values() if v)


def check(steps=200000, sample=20000):
    t, ns = build()
    m = tm.TM(ns, t)
    tape, head, state = {}, 0, 0
    series, ran, halted = [], 0, False
    for i in range(1, steps + 1):
        r = m.step(tape, head, state)
        if r is None:
            halted, ran = True, i
            break
        head, state = r
        ran = i
        if i % sample == 0:
            series.append((i, marks(tape)))
    return dict(states=ns, transitions=len(t), halted=halted, ran=ran,
                series=series)


if __name__ == '__main__':
    table, nstates = build()
    r = check()
    print('2-symbol rung omega: %d transitions, %d states, symbols 0/1'
          % (len(table), nstates))
    print('halting pairs (absent transitions):',
          sorted({s for (s, _) in table}))
    print('halted:', r['halted'], '| steps run:', r['ran'])
    print('marks every 20k steps:', [v for _, v in r['series']])
    first = r['series'][0][1] if r['series'] else 0
    last = r['series'][-1][1] if r['series'] else 0
    mono = all(b >= a for (_, a), (_, b) in zip(r['series'], r['series'][1:]))
    ok = (not r['halted']) and last >= 2 * max(first, 1) and mono
    lines = ['# rung_omega: TWO symbols, never halts, output grows without bound',
             '# 26 states = proved 15-state doubling core + 5 boot writes + 6 walk-back',
             '# core edits: F1 on blank 0 -> 1 (extend U), T2 on blank 0 -> 1 (refill C)',
             '# format: <state> <read> <write> <dir> <next>;  a missing pair means halt']
    lines.append(mk.to_text(table, nstates).rstrip())
    open('machines/rung_omega.txt', 'w').write('\n'.join(lines) + '\n')
    print('emitted machines/rung_omega.txt')
    print('marks %d -> %d (x%.1f), monotone: %s'
          % (first, last, last / max(first, 1), mono))
    print('CHECK', 'PASS' if ok else 'FAIL')
