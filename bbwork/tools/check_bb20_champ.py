"""Check the posted 2-symbol BB(20) champion (20 states x 2 symbols).

Claim (with the machine): halting time is f_(w+7)(f_(w+7)(5)).

Format is bbmulti's loader3229 convention: `_` separates the 20 states in
order A..T, each state lists one 3-char action per read symbol starting at
the blank (0).  Here: A reads 1 -> `---` (no transition: halt) and S reads
0 -> `1RZ` (explicit halt transition Z); those are the two halting rows.

None of these level claims run to halting inside any feasible budget, so
what is measured is bbmulti's probe: (i) no halt inside the budget,
(ii) tape growth at geometric step marks, (iii) that all 20 states and
both symbols are used, (iv) row integrity: the table parses, and the only
undefined/`Z` transitions are the two halt rows listed above.
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bbmulti

TEXT = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..',
                         'machines', 'bb20_2sym_champ.txt')).read()

BUDGET = 20_000_000
MARKS = (1000, 10_000, 100_000, 1_000_000, 10_000_000)


def main():
    table, nst, nsym = bbmulti.parse(TEXT)
    print(f'BB(20) 2-symbol champion   {nst} states x {nsym} symbols, '
          f'{len(table)} transitions')
    steps, halted, score, used_st, used_w, log = bbmulti.run(
        table, BUDGET, MARKS)
    print(f'  halted={halted} after {steps:,} steps, score={score:,}')
    print(f'  states used: {len(used_st)}/{nst}   symbols written: {sorted(used_w)}')
    if log:
        print('  score milestones: ' +
              ', '.join(f'{m:,}@{s:,}' for m, s in log))
    undefined = [(st, sym) for st in 'ABCDEFGHIJKLMNOPQRST'[:nst]
                 for sym in range(nsym) if (st, sym) not in table]
    print(f'  undefined transitions: {len(undefined)}  -> {undefined}')
    rz = [(st, sym) for (st, sym), a in table.items() if a[2] is None]
    print(f'  explicit Z (halt) transitions: {rz}')
    ok = (nst == 20 and nsym == 2 and len(table) == 39
          and len(undefined) == 1 and undefined == [('A', 1)]
          and len(rz) == 1 and rz == [('S', 0)]
          and len(used_st) == 20 and used_w == {0, 1})
    print('ALL OK' if ok else 'PROBE MISMATCH — investigate')


if __name__ == '__main__':
    main()
