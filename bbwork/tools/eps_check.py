"""Identity checks for tools/eps_engine.py.

Each check is a closed-form fact about the fast-growing hierarchy that does not
need the ordinal machinery to state:

    F_0(n)     = n + 1
    F_1(n)     = 2n + 1
    F_2(n)     = 2^(n+1) * (n+1) - 1
    F_w(n)     = F_n(n)                       (definition, cross-checked)
    eps_0[2]   = w^w                          (height-2 tower)
    (w^2 + w)[4] = w^2 + 4

The last two checks are budget-aware: F_w(3) = F_3(3) is far beyond any feasible
computation, so "both sides exceed the work cap" is the correct assertion there.

Exit status 0 iff every check passes.
"""

import sys

sys.path.insert(0, 'tools')
import eps_engine as E

FAILED = []


def chk(name, got, want):
    ok = got == want
    print(f'  {name}: {got} vs {want} {"PASS" if ok else "FAIL"}')
    if not ok:
        FAILED.append(name)


def budget(fn):
    try:
        return ('value', fn())
    except E.Budget:
        return ('budget', None)
    except RecursionError:
        return ('depth', None)


def main():
    for n in range(6):
        chk(f'F0({n})', E.F(E.ZERO, n, [10000]), n + 1)
        chk(f'F1({n})', E.F(E.nat(1), n, [10000]), 2 * n + 1)
        chk(f'F2({n})', E.F(E.nat(2), n, [10000]), 2 ** (n + 1) * (n + 1) - 1)

    w = E.omega(E.nat(1))                      # omega = omega^1
    for n in (0, 1, 2):
        chk(f'Fw({n}) = F{n}({n})', E.F(w, n, [200000]), E.F(E.nat(n), n, [200000]))

    # F_w(3) = F_3(3): both must blow the cap rather than disagree
    a = budget(lambda: E.F(w, 3, [200000]))
    b = budget(lambda: E.F(E.nat(3), 3, [200000]))
    chk('Fw(3) and F3(3) both exceed the cap', a[0], b[0])
    chk('...and neither produced a value', a[0] in ('budget', 'depth'), True)

    chk('eps0[2] = w^w', E.fs_eps0(2), E.omega(w))
    chk('eps0[3] = w^(w^w)', E.fs_eps0(3), E.omega(E.omega(w)))
    chk('(w^2+w)[4]', E.show(E.fs(((1, E.nat(2)), (1, E.nat(1))), 4), 99), 'w^2+4')
    chk('(w^w)[3]', E.show(E.fs(E.omega(w), 3), 99), 'w^3')

    print('ALL OK' if not FAILED else f'FAILURES: {FAILED}')
    return 0 if not FAILED else 1


if __name__ == '__main__':
    sys.exit(main())
