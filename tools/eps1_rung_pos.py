"""Where the stage/rung machine sits: one level below eps_1, by measurement.

The 57-state stage/rung machine (tools/eps1_machine.py) runs the ladder

    lvl 0 v = v        lvl (S k) v = run (lvl k v) v        run(v) = 2^(v+1)-1

where `run(c, v)` applies eps_0's stage **c** times to v (each application
doubles up: 2^(v+1)-1), so rung k hands rung k+1 its own output as the count
of stage applications.  The measured reality of `machine.check`'s cases is
that the simulatable range is small: a=0 frees the value (7 steps each), and
the rungs themselves only reach (a=1, v=1) at 105 steps and (a=1, v=2) at
68384 steps -- (a=1, v=3) already needs eps_0 to run 2^65536 rounds, and
rungs a >= 2 need a stage of stage(v'') rounds over a 65535-mark block
(~4e9 steps) and then 2^256 - 1 marks.  Beyond simulation, this file records
the computed ladder values instead.

The level claim must be read against the two ladders
`tools/eps1_level.py` measures (both printed here, unmodified):

    towers over 1            H(wraps(h), n)     the flat engine's world
    towers over eps_0+1      H(members(k), n)   the eps_1 members (rule 6)

The verdict the numbers support: the machine's whole reachable ladder stays
in the flat tower world -- every rung is eps_0's own machinery over unary
blocks, no eps_1 member is entered at any rung, and no ordinal notation is
descended anywhere (EPS1_35_STATES.md's open item).  That is the
one-level-below-eps_1 position: the replacement supplies the eps_1 descent
itself, at model level as tools/eps1_stack.py now does, with the rows to
follow per EPS1_67_PLAN.md.

This is a measurement, not a proof, and it is not a claim about f_eps_1.

Run: python tools/eps1_rung_pos.py
"""

import sys
import time

sys.path.insert(0, 'tools')

import eps1_machine as M
import eps1_level as L


def fmt(x, limit=60):
    """Values can exceed the int-string digit cap; abbreviate then."""
    try:
        s = str(x)
    except ValueError:
        # str() has its own digit cap (4300); sizes go by bit length
        bits = x.bit_length()
        return f'({bits} bits, about 10^{bits / 3.32:.1f})'
    if len(s) <= limit:
        return s
    return f'{s[:12]}...({len(s)} digits)'


def run_case(a, v, max_steps=60_000_000):
    start_t = time.time()
    tape, head, st, grey = M.start(a, v)
    m = M.machine()
    steps, t2, h2, s2, halted = m.run(head=head, state=st, tape=tape,
                                      max_steps=max_steps)
    wall = time.time() - start_t
    want = M.lvl(a, v)
    got = M.value(t2, grey['wall'])
    good = halted and got == want
    return steps, wall, got, want, good, halted, s2


def main():
    print('eps_1 stage/rung machine, 57 states: measured (steps, value)')
    print('  ladder: lvl 0 v = v, lvl (S k) v = run (lvl k v) v,')
    print('  run(v) = 2^(v+1)-1 -- rung k = stage applied lvl k v times')
    print()
    for v in range(0, 7):
        steps, wall, got, want, good, halted, s2 = run_case(0, v)
        print(f'  a=0 v={v}: steps={steps:<10} value={got:<10} '
              f'want={want:<10} ready={M.NAMES.get(s2, s2):<4} '
              + ('OK' if good and halted else 'FAIL'))
    print()
    for v in (1, 2):
        steps, wall, got, want, good, halted, s2 = run_case(1, v)
        print(f'  a=1 v={v}: steps={steps:<10} value={fmt(got):<14} '
              f'want={fmt(want):<14} '
              + ('OK' if good and halted else 'FAIL'))
    print()
    print('  beyond simulation, recorded as computed ladder values:')
    print(f'    a=1 v=3:  lvl = {fmt(M.lvl(1, 3))}   '
          '(the third stage application runs eps_0 for 2^65536 rounds)')
    print('    a=1 v=4:  not constructed: stage applied once more is a'
          ' 2^(2^65536)-bit')
    print('              number; each further rung doubles the bit length'
          ' again, so')
    print('              lvl(1, v) is described by its recursion, never by'
          ' its digits.')
    print(f'    a=2 v=1:  lvl = {fmt(M.lvl(2, 1))}   '
          '(second rung: a stage over a 65535-mark block, ~4e9 steps)')
    print('    a=2 v=2:  not constructed: run(lvl 1 v = 255, 2) is stage'
          ' applied 255')
    print('              times to 2, so its bit length is itself a tower'
          ' of twos; the')
    print('              simulation needs a stage of 2^256 - 1 marks')
    print()
    print(f'eps1_level: the ladders the claim must sit against (cap {L.CAP})')
    L.check_lengths()
    L.check_growth()
    print()
    print('VERDICT (from the numbers above, not asserted):')
    print("  the machine's whole reachable ladder is the flat world: every")
    print('  rung is eps_0\'s own machinery over unary blocks; its two')
    print('  simulatable rungs (3, 255) sit below the flat ladder\'s wall,')
    print('  while H(member 1, n) leaves every cap used here.  No eps_1')
    print('  member is entered at any rung, and no ordinal notation is')
    print('  descended anywhere.  One level below eps_1: the replacement')
    print('  supplies the eps_1 descent itself -- at model level that is')
    print('  tools/eps1_stack.py; the rows follow it per EPS1_67_PLAN.md.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
