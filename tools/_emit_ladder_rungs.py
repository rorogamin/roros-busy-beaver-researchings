"""Emit the next two verified ladder rungs: c=11 (Machine6) and c=13 (Machine7).

The five machines in rocq/Machine1..5 cover c=8,10,12 of the boot+core family.
This writes the missing c=11 rung and the next c=13 rung, with the exact halt
count measured by tools/tm.py and a Rocq proof emitted by tools/emit_rocq.py.

Run from bbwork:  python tools/_emit_ladder_rungs.py
Then:             cd rocq && rocq compile -Q . Top Machine6.v
                  cd rocq && rocq compile -Q . Top Machine7.v
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import mk_machines as mk
import emit_rocq as E

ROWS = [
    (11, 'Machine6', 'machine_6_omega', 4096),
    (13, 'Machine7', 'machine_7_omega', 16384),
]


def main():
    os.chdir(os.path.join(ROOT, 'rocq'))
    for c, mod, fname, claim in ROWS:
        tbl, n = mk.machine1(c, 2, 1)
        path = os.path.join('..', 'machines', fname + '.txt')
        with open(path, 'w') as f:
            f.write(mk.to_text(tbl, n))
        E.emit(fname, mod,
               f'Machine {mod[-1]}: exponential-growth blank-tape machine',
               c, 2, 1, claim, extra_tower=3)


if __name__ == '__main__':
    main()
