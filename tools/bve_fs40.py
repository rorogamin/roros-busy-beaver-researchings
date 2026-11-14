"""Bind the general BVE FS driver to the 40-state predecessor quotient.

This does NOT make the general FS arm a 5-tuple table.  It reroutes the
duplicate-flag predecessor route of `bve_fs.composed_step` from the 46-state
compose table to `bve_compose40`, then runs the existing general-arm checks:
200 limit terms, 200 composed steps, and the bounded 43-term descent.

So the result is a measured composition of:
  * the 40-state real BVE cursor/predecessor table, and
  * the general flag-0 FS arm (still the semantic tape-level arm in
    `bve_fs.py`).

Run: python tools/bve_fs40.py
"""

import sys
sys.path.insert(0, 'tools')

import bve_compose
import bve_compose40
import bve_fs


def main():
    old_table, old_n = bve_compose.TABLE, bve_compose.N_STATES
    bve_compose.TABLE = bve_compose40.TABLE
    bve_compose.N_STATES = bve_compose40.N_STATES
    try:
        ok1 = bve_fs.check(n_terms=200)
        ok2 = bve_fs.check_descent(n_terms=30, cap=40)
    finally:
        bve_compose.TABLE, bve_compose.N_STATES = old_table, old_n
    ok = ok1 and ok2
    print()
    print('scope: general flag-0 FS is semantic; no general 5-tuple FS table')
    print('40-state predecessor + general semantic FS: '
          + ('ALL OK' if ok else 'FAILURES'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
