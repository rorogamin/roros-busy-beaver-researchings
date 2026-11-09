"""The eps_0 descent in borrow/push form, tied to eps1_full's model exactly.

The verified recordings:

  * `tools/eps1_full.py` -- the whole tower descent as a 2-symbol table.  Its
    moves are checked move-for-move against `tools/tower_free.step` (its own
    `check_moves`, green in the gate), and tower_free is checked against
    `tools/tower_rules` over every chain up to depth 4 (tower_free's check).
  * `tools/eps1_chain.py` -- the eps_1 rule set of record, checked against the
    ordinal model, and re-derived as the local stack model in
    `tools/eps1_stack.py` (bookkeeping-exact over 400 chains x 4 moves).

This file states the fusion claim of EPS1_67_PLAN.md's open question 1 at
model level: the eps_0 descent (tower_free, and with it eps1_full) is the
same bookkeeping as eps1_chain on the plain-numeral world, connected by
`model_of`-style relabeling.  In borrow/push vocabulary:

    eps1_chain (p, chain)          tower_free (m, W)      the verb

    p wraps, chain's top >= 2,     m >= 1, W nonempty     WRAP-SPEND (B):
      p -= 1, chain := head ++ [n+1]                     site below the wraps
                                        m-1, W := [n+1, W[0]-1] ++ W[1:]
    p == 0, chain's top >= 2       m == 0, W nonempty     BORROW (A):
      chain := pred_chain(chain)                          W[0] -= 1
    chain's val a limit            site below the block   REFILL: the n+1
      chain_fs at the site                                write at the site
    chain = [] for eps1_chain      W empty, m >= 2        PUSH (new rung):
      (halt next move)                                   m-2, W := [n+1]

The atom cases of eps1_chain ([ATOM] = eps_0, [ATOM1] = eps_0 + 1) are the
push at the eps_1 bottom (the fs-limit); they are not in tower_free's world
and are covered by the stack model instead.

The one convention difference, stated so nobody conflates it: tower_free (and
with it eps1_full) freezes the index n as a machine constant; eps1_chain (the
eps_1 obligation of record) bumps it at every predecessor.  So the exact
statement checked here is: tower_free == eps1_chain-with-frozen-index,
exhaustively over the plain-numeral world.  The eps_1 stack machine must
therefore supply the running index separately -- that is EPS1_67_PLAN.md's
open question 2 (where the index lives), which the stack model handles as a
return value and the tape will have to handle as a structure.

Run: python tools/eps0_fusion.py
"""

import sys
import itertools

sys.path.insert(0, 'tools')

import eps1_descent as D
import eps1_chain as C
import eps1_descent as DD   # alias for the fs/pred/tests
import tower_free as TF

NUM = lambda c: D.Ord(((D.ZERO, c),))


# --------------------------------------------------- the flattening relabeling

def to_tower_free(p, chain):
    """(p, chain) -> tower_free's full top-first run list."""
    c0 = chain[0].terms[0][1]
    assert len(chain[0].terms) == 1 and chain[0].terms[0][0] == D.ZERO
    ints = [c0] + [int(x) for x in chain[1:]]
    return [1] * p + list(reversed(ints))


def from_tower_free(T):
    """A stepped top-first run list -> (m, chain), canonical, bottom as NUM.

    tower_free's all-unit world has no chain to keep, so canonicalise it
    like eps1_chain's own guard does: the bottom unit rung stays in the
    chain as [NUM(1)], and the tower of (m-1) further omegas is the wraps.
    """
    m, W = TF.split(T)
    if not W:
        if m == 0:
            return 0, []
        return m - 1, [NUM(1)]
    cp = list(reversed(W))                      # bottom-first integers
    return m, [NUM(cp[0])] + cp[1:]


# ------------------------------------------- eps1_chain's step, index frozen

def frozen_step(p, chain, n):
    """eps1_chain.step with the Hardy bump removed.

    This is deliberately eps1_chain's own case analysis, reusing its helpers,
    so the only delta from `eps1_chain.step` is the index convention.  With
    the freeze, the move shapes are exactly tower_free's.
    """
    if not chain:
        raise C.Halt
    if C.is_succ(chain):
        head = C.pred_chain(chain)
        if p == 0:
            return C.normalise(0, head)
        chain2 = (head + [n + 1]) if head else [NUM(n + 1)]
        return C.normalise(p - 1, chain2)
    p2, c2 = C.normalise(p, C.chain_fs(chain, n))
    return p2, c2


# -------------------------------------------------------------------- checks

def check_tower_equals_chain_frozen(c0max=3, maxlen=3, pmax=2, ns=(1, 2, 3),
                                    tailmax=3):
    print('the flat world is eps1_chain with a frozen index:')
    print('  tower_free.step == frozen_step, exhaustively over the product')
    tested = halted = 0
    bad = 0
    for depth in range(1, maxlen + 1):
        for c0 in range(1, c0max + 1):
            for tail in itertools.product(range(1, tailmax + 1),
                                          repeat=depth - 1):
                chain = [NUM(c0)] + list(tail)
                for p in range(0, pmax + 1):
                    for n in ns:
                        # eps1_chain side, index frozen; the drained pair
                        # (p, []) means the next move halts, so it rises to
                        # tower_free's None
                        try:
                            fp, fc = frozen_step(p, chain, n)
                            fst = 'zero' if not fc else (fp, fc)
                        except C.Halt:
                            fst = 'zero'
                        # tower_free side
                        T = TF.step(to_tower_free(p, chain), n)
                        if T is None:
                            tst = 'zero'
                        else:
                            m2, ch2 = from_tower_free(T)
                            tst = 'zero' if not ch2 else (m2, ch2)
                        tested += 1
                        if fst != tst:
                            bad += 1
                            print(f'  HALT MISMATCH p={p} chain={chain} n={n}')
                            if bad > 10:
                                raise SystemExit(1)
                            continue
                        if fst == 'zero':
                            halted += 1
                            continue
    print(f'  {tested} states ({halted} halting): '
          + ('OK, exact' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_lengths(cases):
    print()
    print('run lengths: frozen_step and tower_free.descents agree to 0')
    ok = True
    for p, chain, n in cases:
        sp, sc = p, list(chain)                 # keep the start for the print
        T = to_tower_free(p, chain)
        moves = 0
        try:
            while True:
                p, chain = frozen_step(p, chain, n)
                moves += 1
                if moves > 500000:
                    moves = None
                    break
        except C.Halt:
            pass
        s, pm, dm = TF.descent(T, n, limit=500000)
        same = moves == s
        ok = ok and same
        print(f'    p={sp} chain={sc} n={n}: frozen {moves} '
              f'tower_free {s} {"OK" if same else "MISMATCH"}')
    return ok


def show_index_convention(start, n):
    """Print where the bumped index diverges from the frozen one, and why."""
    print('  the convention difference, shown on one run:')
    p, chain = start
    pb, cb = p, list(chain)
    pf, cf = p, list(chain)
    nb = n
    i = 0
    while True:
        i += 1
        try:
            pb, cb, nb, _ = C.step(pb, cb, nb)
        except C.Halt:
            print(f'    move {i}: eps1_chain halts (bumped index)')
            break
        try:
            pf, cf = frozen_step(pf, cf, n)
        except C.Halt:
            print(f'    move {i}: frozen halts; eps1_chain does not')
            break
        where = (pb, cb) != (pf, cf)
        if where:
            print(f'    the first move whose states differ is move {i}')
            print(f'      bumped index  -> ({pb}, {cb}) with index {nb}')
            print(f'      frozen index  -> ({pf}, {cf})            index {n}')
            print('      the n+1 written at the site differs from then on:')
            print('      the flat world re-starts its count every rung, the'
                  ' Hardy index')
            print('      keeps growing -- the eps_1 stack machine must carry '
                  'the running')
            print('      index as its own structure (EPS1_67_PLAN.md, '
                  'question 2).')
            break


def main():
    ok = check_tower_equals_chain_frozen()
    # a start whose fs fires right after a pred: that is the only place the
    # bumped and frozen indices differ
    show_index_convention((0, [NUM(1), 2]), 2)
    print()
    ok = check_lengths([(0, [NUM(2)], 1), (0, [NUM(3)], 1), (0, [NUM(2), 2], 1),
                        (2, [NUM(2), 2], 1), (0, [NUM(2), 1, 2], 2)]) and ok
    print()
    print('eps1_full ties in already: its own check_moves is move-for-move '
          'against')
    print('tower_free (green in the gate), so the machine, tower_free and '
          'eps1_chain')
    print('with a frozen index are one semantics on the plain-numeral world.')
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
