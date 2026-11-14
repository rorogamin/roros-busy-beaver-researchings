"""Flag-0 fundamental-sequence arm for the two-bank rBVE tape.

This is a tape-level semantic arm, not a 5-tuple transition table.  It decodes
the term field, applies the checked BVE oracle `eps1_bve.model_fs`, and
re-encodes the result.  The composed step driver uses it for flag-0 limit
terms; duplicate-flag predecessors go through the 46-state `bve_compose` table.

The arm is deliberately explicit about its boundary: it does not copy or build
an exponent on the tape and does not yet carry an index field.  It is the
semantic target the eventual FS transition arm must match.

Run: python tools/bve_fs.py
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
import bve_two_bank as T
import bve_fs_simple

# Imported lazily by composed_step so importing this module does not import
# the composed table in a cycle.


def term_tape(v):
    return T.to_tape(v)


def tape_string(tape):
    lo = min(tape) if tape else 0
    hi = max(tape) if tape else 0
    return ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def fs_tape(tape, n):
    """Expand a flag-0 limit term by one fundamental-sequence step."""
    v = T.from_tape(tape)
    if not B.model_is_limit(v):
        raise ValueError(f'not a flag-0 limit term: {v!r}')
    new = B.model_fs(v, n)
    out = T.to_tape(new)
    if T.from_tape(out) != new:
        raise AssertionError('FS tape did not round-trip')
    return out


def composed_step(tape, n):
    """One step of the composed driver.

    Returns (tape, n, kind).  This is a semantic composition: the 46-state
    table performs the duplicate-flag predecessor route, while flag-0 limits
    use fs_tape and flag-0 successors use the semantic predecessor.  The
    predecessor arm's gap state lets it consume its own raw output; no term
    re-encoding is needed on that route.
    """
    v = T.from_tape(tape)
    if v.is_zero():
        return tape_string(tape), n, 'halt'

    if B.model_is_limit(v):
        # The first real 5-tuple FS arm covers exactly omega[1] = 2.
        if v == bve_fs_simple.SIMPLE and n == bve_fs_simple.N \
                and tape == bve_fs_simple.INPUT:
            cells = {i: int(c) for i, c in enumerate(tape)}
            ok, out, head, state, steps = bve_fs_simple.run(cells)
            if not ok:
                raise AssertionError('simple FS table did not halt')
            return bve_fs_simple.tape_string(out), n, 'fs'
        return fs_tape(tape, n), n, 'fs'

    if len(v.terms) >= 2 and v.terms[-1] == v.terms[-2]:
        import bve_compose
        cells = {i: int(c) for i, c in enumerate(tape)}
        ok, out, head, state, steps = bve_compose.run(
            cells, bve_compose.h_end_of(v))
        if not ok:
            raise AssertionError(f'composed pred table did not halt: {v!r}')
        got = T.from_tape(tape_string(out))
        want = B.pred(v)
        if got != want:
            raise AssertionError(
                f'composed pred mismatch: got {got!r}, want {want!r}')
        # The predecessor arm normalises the H/E zero gap on entry, so the
        # raw tape can be fed directly to the next predecessor.  This keeps
        # the table composition continuous instead of re-encoding the term.
        return tape_string(out), n + 1, 'pred'

    # A flag-0 successor (the last principal is 1 or the epsilon_0 atom in a
    # sum) is a predecessor.  The current table does not route this case, so
    # the driver uses the semantic predecessor as the temporary fallback.
    return T.to_tape(B.pred(v)), n + 1, 'pred'


def descent(tape, n, cap=200):
    """Run composed semantic steps to zero; return (value_or_None, steps).

    The cap and step accounting match `B.hardy`: increment, then stop if the
    count exceeds the cap.
    """
    steps = 0
    while True:
        v = T.from_tape(tape)
        if v.is_zero():
            return n, steps
        steps += 1
        if steps > cap:
            return None, steps
        tape, n, _kind = composed_step(tape, n)


def check_descent(n_terms=30, cap=40):
    """Bounded end-to-end descent check against the oracle.

    The corpus is deliberately shallow on the random side.  Deep epsilon
    towers are already exercised by the semantic FS checks above; encoding a
    tall tower as tape cells and decoding it at every step is much slower than
    the oracle, so a broad depth-2 corpus would test the codec's size limit
    rather than the composed transition policy.
    """
    rng = random.Random(67)

    def term(d):
        if d <= 0:
            return rng.choice((ZERO, ONE))
        k = rng.randrange(4)
        if k == 0:
            return phi(0, term(d - 1))
        if k == 1:
            return phi(1, term(d - 1))
        if k == 2:
            return add(term(d - 1), term(d - 1))
        return add(phi(0, term(d - 1)), term(d - 1))

    fixed = [
        (ZERO, 0), (ONE, 0), (ONE, 1),
        (phi(0, ONE), 1), (phi(0, ONE), 2), (phi(0, ONE), 3),
        (add(phi(0, ONE), ONE), 0),
        (phi(0, phi(0, ONE)), 0), (phi(0, phi(0, ONE)), 1),
        (B.epsilon0(), 0), (B.epsilon0(), 1), (B.epsilon1(), 0),
        # Deliberate cap case: both sides should stop at cap + 1 steps.
        (add(phi(0, ONE), phi(1, ZERO)), 1),
    ]
    terms = list(fixed)
    while len(terms) < len(fixed) + n_terms:
        terms.append((term(1), 0))

    bad = 0
    checked = 0
    for idx, (v, n) in enumerate(terms):
        want_v, want_steps = B.hardy(v, n, cap=cap)
        try:
            got_v, got_steps = descent(term_tape(v), n, cap=cap)
        except Exception:
            print(f'  DESCENT EXCEPTION {idx}: {v!r} n={n}')
            print(f'    start {term_tape(v)}')
            raise
        if (got_v, got_steps) != (want_v, want_steps):
            bad += 1
            print(f'  DESCENT FAIL {idx}: {v!r} n={n}')
            print(f'    got  {(got_v, got_steps)!r}')
            print(f'    want {(want_v, want_steps)!r}')
        else:
            checked += 1
    print(f'  descent: {checked}/{len(terms)} terms match B.hardy '
          f'(cap {cap})' + ('' if bad == 0 else f'; {bad} FAILURES'))
    return bad == 0


def check(n_terms=200):
    rng = random.Random(53)

    def term(d):
        if d <= 0:
            return rng.choice((ZERO, ONE))
        k = rng.randrange(4)
        if k == 0:
            return phi(0, term(d - 1))
        if k == 1:
            return phi(1, term(d - 1))
        if k == 2:
            return add(term(d - 1), term(d - 1))
        return add(phi(0, term(d - 1)), term(d - 1))

    fixed = [B.epsilon0(), B.epsilon1(), phi(0, ONE),
             phi(0, phi(0, ONE)), phi(1, ONE), phi(1, ZERO),
             add(phi(0, ONE), phi(1, ZERO))]
    terms = [v for v in fixed if B.model_is_limit(v)]
    while len(terms) < n_terms:
        v = term(3)
        if B.model_is_limit(v):
            terms.append(v)

    bad = 0
    counts = {'fs': 0, 'pred': 0, 'halt': 0}
    for idx, v in enumerate(terms):
        n = 1 + (idx % 2)
        tape = term_tape(v)
        out = fs_tape(tape, n)
        got = T.from_tape(out)
        want = B.model_fs(v, n)
        if got != want:
            bad += 1
            print(f'  FS FAIL {idx}: {v!r} n={n}')
            print(f'    got  {got!r}')
            print(f'    want {want!r}')
            continue
        # The arm must strictly decrease the term.
        if B._cmp_v(got, v) >= 0:
            bad += 1
            print(f'  NO DECREASE {idx}: {v!r} -> {got!r}')
        counts['fs'] += 1

    # Drive the composed step on both limit and predecessor examples.
    step_terms = [B.epsilon0(), B.epsilon1(), phi(0, ONE),
                  phi(0, phi(0, ONE)), add(phi(0, ONE), ONE),
                  add(ONE, ONE), phi(1, ZERO)]
    while len(step_terms) < n_terms:
        step_terms.append(term(3))
    for idx, v in enumerate(step_terms):
        n = 1 + (idx % 2)
        tape = term_tape(v)
        out, n2, kind = composed_step(tape, n)
        want_v, want_n, want_kind = B.model_step(v, n)
        got_v = T.from_tape(out)
        if (got_v, n2, kind) != (want_v, want_n, want_kind):
            bad += 1
            print(f'  COMPOSED FAIL {idx}: {v!r} n={n}')
            print(f'    got  {(got_v, n2, kind)!r}')
            print(f'    want {(want_v, want_n, want_kind)!r}')
        else:
            counts[kind] += 1

    print(f'  FS arm: {len(terms)} limit terms; '
          f'composed step: {len(step_terms)} terms: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    print(f'  routes: {counts}')
    return bad == 0


def example():
    for label, v in [('omega^omega', phi(0, phi(0, ONE))),
                     ('epsilon_0', B.epsilon0()),
                     ('epsilon_1', B.epsilon1())]:
        n = 1
        tape = term_tape(v)
        out = fs_tape(tape, n)
        print(f'example: {label} [{n}]')
        print(f'  in  {v!r}')
        print(f'  out {T.from_tape(out)!r}')
        print(f'  fs  {B.model_fs(v, n)!r}')


def main():
    ok = check()
    d_ok = check_descent()
    ok = d_ok and ok
    if ok:
        print()
        example()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
