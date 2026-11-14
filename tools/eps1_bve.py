"""Binary Veblen engine (BVE): a 2-bit postfix term system for epsilon_1.

The design target is a 2-symbol TM.  Instead of encoding epsilon_0 as a list of
lists and parsing field positions, a term is a binary Veblen tree:

    00  =  0
    01  =  1
    10  =  phi_0(a) + b  =  w^a + b
    11  =  phi_1(a) + b  =  e_a + b

The four tokens are two bits each, so the tape alphabet is still {0,1}.  A
term is postfix: `a b 10` is phi_0(a)+b.  The right child b is the additive
tail, so the tree is self-delimiting.  phi_0/phi_1 close at epsilon_1:
phi_1(1) = epsilon_1, and no phi_2 is present.

This module is the proof-of-concept rewriter, not the TM table.  It provides:
  * parse/render of token strings;
  * ordinal comparison for the Veblen normal forms;
  * pred/fs operations (standard fundamental sequences);
  * an encoding back to the 2-bit token string;
  * checks that epsilon_1[n] is the repo model's `tower(n)`, and that the
    first descent moves agree with tools/eps1_descent.py on the common
    (tower-over-epsilon_0+1) fragment.

Run: python tools/eps1_bve.py
"""

import random
import sys
from dataclasses import dataclass
from functools import cmp_to_key

sys.path.insert(0, 'tools')

import eps1_descent as D

ZERO_TOK = '00'
ONE_TOK = '01'
PHI0_TOK = '10'
PHI1_TOK = '11'
TOKENS = (ZERO_TOK, ONE_TOK, PHI0_TOK, PHI1_TOK)


@dataclass(frozen=True)
class V:
    """A Veblen normal form: principal terms in non-increasing order."""

    terms: tuple

    def is_zero(self):
        return not self.terms

    def __repr__(self):
        if self.is_zero():
            return '0'
        out = []
        for p in self.terms:
            if p.i == 0:
                out.append('w^(' + repr(p.a) + ')')
            else:
                out.append('e(' + repr(p.a) + ')')
        return ' + '.join(out)


@dataclass(frozen=True)
class P:
    """A principal term phi_i(a)."""

    i: int
    a: V


ZERO = V(())
ONE = V((P(0, ZERO),))


def phi(i, a):
    assert i in (0, 1)
    return V((P(i, a),))


def _cmp_v(a, b):
    """Compare two Veblen normal forms.  Returns -1, 0, 1."""
    for pa, pb in zip(a.terms, b.terms):
        c = _cmp_p(pa, pb)
        if c:
            return c
    if len(a.terms) < len(b.terms):
        return -1
    if len(a.terms) > len(b.terms):
        return 1
    return 0


def _cmp_p(p, q):
    """Compare phi_i(a) with phi_j(b), for i,j in {0,1}.

    Veblen comparison:
      i == j: compare a and b;
      i <  j: phi_i(a) < phi_j(b) iff a < phi_j(b);
      i >  j: phi_i(a) < phi_j(b) iff phi_i(a) < b.
    """
    if p.i == q.i:
        return _cmp_v(p.a, q.a)
    if p.i < q.i:
        return _cmp_v(p.a, V((q,)))
    return _cmp_v(V((p,)), q.a)


def _sort_terms(terms):
    return tuple(sorted(terms, key=cmp_to_key(_cmp_p), reverse=True))


def add(a, b):
    """Veblen normal-form addition.  Coefficients are repeated principals."""
    if a.is_zero():
        return b
    if b.is_zero():
        return a
    return V(_sort_terms(a.terms + b.terms))


def is_successor(a):
    """The last principal term is 1 = phi_0(0)."""
    return bool(a.terms) and a.terms[-1].i == 0 and a.terms[-1].a.is_zero()


def is_limit(a):
    """Standard ordinal limit (coefficients do not count as successors)."""
    return not a.is_zero() and not is_successor(a)


def pred(a):
    """Remove one copy of the last principal term.

    This is the predecessor for a term whose last principal is 1, and also for
    the oracle's coefficient-descent policy (c > 1 -> c - 1).
    """
    assert a.terms, a
    last = a.terms[-1]
    assert (len(a.terms) >= 2 and a.terms[-2] == last) or \
           (last.i == 0 and last.a.is_zero()) or \
           (last.i == 1 and last.a.is_zero()), a
    return V(a.terms[:-1])


def model_is_limit(a):
    """The oracle's descent policy: a top coefficient > 1 is a predecessor."""
    if a.is_zero():
        return False
    last = a.terms[-1]
    if len(a.terms) >= 2 and a.terms[-2] == last:
        return False
    if last.i == 0 and last.a.is_zero():
        return False
    # The atom E0 is a limit only as the whole term.  In a sum, the oracle's
    # predecessor policy removes it, exactly as D.is_limit does for e is None.
    if last.i == 1 and last.a.is_zero() and len(a.terms) > 1:
        return False
    return True


def model_fs(a, n):
    """The oracle's fs, including coefficient descent in exponents.

    eps1_descent.is_limit treats w^e * c with c > 1 as non-limit, and its fs
    then applies pred(e).  This mirrors that policy recursively.
    """
    assert model_is_limit(a), a
    head = V(a.terms[:-1])
    p = a.terms[-1]

    if p.i == 0:
        b = p.a
        assert not b.is_zero()
        if model_is_limit(b):
            new = phi(0, model_fs(b, n))
        else:
            new = V((P(0, pred(b)),) * (n + 1))
    else:
        b = p.a
        if b.is_zero():
            new = tower_over(ONE, n)
        elif model_is_limit(b):
            new = phi(1, model_fs(b, n))
        else:
            base = add(phi(1, pred(b)), ONE)
            new = tower_over(base, n)

    return add(head, new)


def model_step(a, n):
    """One oracle-policy move; returns (next, next_n, kind)."""
    if model_is_limit(a):
        return model_fs(a, n), n, 'fs'
    return pred(a), n + 1, 'pred'


def tower_over(base, n):
    """phi_0 applied n times to base."""
    v = base
    for _ in range(n):
        v = phi(0, v)
    return v


def fs(a, n):
    """The n-th member of the fundamental sequence of a limit term."""
    assert is_limit(a), a
    assert n >= 0
    head = V(a.terms[:-1])
    p = a.terms[-1]

    if p.i == 0:
        b = p.a
        assert not b.is_zero(), 'phi_0(0) is 1, not a limit'
        if is_successor(b):
            # w^(b'+1) = w^b' * (n+1)
            new = V((P(0, pred(b)),) * (n + 1))
        else:
            # w^b, b limit: w^(b[n])
            new = phi(0, fs(b, n))
    else:
        b = p.a
        if b.is_zero():
            # e_0[n] = tower of n omegas over 1
            new = tower_over(ONE, n)
        elif is_successor(b):
            # e_(b'+1)[n] = tower of n omegas over e_b' + 1
            base = add(phi(1, pred(b)), ONE)
            new = tower_over(base, n)
        else:
            # e_b, b limit: e_(b[n])
            new = phi(1, fs(b, n))

    return add(head, new)


def hardy(a, n, cap=200_000):
    """Descend to zero under the oracle policy.  Returns (value, steps)."""
    steps = 0
    while not a.is_zero():
        steps += 1
        if steps > cap:
            return None, steps
        a, n, _ = model_step(a, n)
    return n, steps


# ------------------------------------------------------------------ encoding

def encode(a):
    """Encode a term as a postfix 2-bit token string."""
    if a.is_zero():
        return ZERO_TOK
    if a == ONE:
        return ONE_TOK
    p = a.terms[0]
    rest = V(a.terms[1:])
    op = PHI0_TOK if p.i == 0 else PHI1_TOK
    return encode(p.a) + encode(rest) + op


def parse(s):
    """Parse a postfix 2-bit token string into a V term."""
    if len(s) % 2:
        raise ValueError('token string has odd length')
    chunks = [s[i:i + 2] for i in range(0, len(s), 2)]
    stack = []
    for k, t in enumerate(chunks):
        if t == ZERO_TOK:
            stack.append(ZERO)
        elif t == ONE_TOK:
            stack.append(ONE)
        elif t in (PHI0_TOK, PHI1_TOK):
            if len(stack) < 2:
                raise ValueError(f'missing operands at token {k}')
            b = stack.pop()
            a = stack.pop()
            i = 0 if t == PHI0_TOK else 1
            stack.append(add(phi(i, a), b))
        else:
            raise ValueError(f'bad token {t!r} at {k}')
    if len(stack) != 1:
        raise ValueError(f'stack has {len(stack)} terms at end')
    return stack[0]


# ------------------------------------------------------- bridge to eps1 model

def to_d(a):
    """Map the tower-over-epsilon_0+1 fragment to eps1_descent.Ord.

    Only phi_1(0) is allowed; phi_1(a), a > 0, is outside that model.
    """
    out = D.ZERO
    for p in a.terms:
        if p.i == 0:
            out = D.add(out, D.mul_pow(to_d(p.a), 1))
        else:
            if not p.a.is_zero():
                raise ValueError(f'not in the tower fragment: {a!r}')
            out = D.add(out, D.E0)
    return out


def tower_fragment(a):
    try:
        to_d(a)
        return True
    except ValueError:
        return False


def epsilon1():
    return phi(1, ONE)


def epsilon0():
    return phi(1, ZERO)


def epsilon0_plus_one():
    return add(epsilon0(), ONE)


# -------------------------------------------------------------------- checks

def check_roundtrip():
    print('token round-trip')
    terms = [ZERO, ONE, epsilon0(), epsilon0_plus_one(), epsilon1(),
             phi(0, ONE), phi(0, phi(0, ONE)), phi(1, add(epsilon1(), ONE)),
             add(phi(0, ONE), ONE), add(epsilon0(), phi(0, ONE))]
    bad = 0
    for a in terms:
        s = encode(a)
        b = parse(s)
        ok = a == b
        bad += not ok
        print(f'  {s:<24} {a!r:<38} -> {b!r}  {"OK" if ok else "FAIL"}')
    print('  ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_epsilon1_sequence():
    print()
    print('epsilon_1[n] against eps1_descent.tower(n)')
    bad = 0
    for n in range(0, 5):
        v = fs(epsilon1(), n)
        want = D.tower(n)
        got = to_d(v)
        ok = got == want
        bad += not ok
        print(f'  n={n}: {encode(v):<28} -> {v!r}')
        print(f'       model {want!r}  {"OK" if ok else "FAIL"}')
    return bad == 0


def check_epsilon0_sequence():
    print()
    print('epsilon_0[n] against eps1_descent.wraps(n)')
    bad = 0
    for n in range(0, 4):
        v = fs(epsilon0(), n)
        want = D.wraps(n)
        got = to_d(v)
        ok = got == want
        bad += not ok
        print(f'  n={n}: {v!r}  {"OK" if ok else "FAIL"}')
    return bad == 0


def check_descent():
    print()
    print('first descent from epsilon_1[2], checked against the eps1 model')
    v = fs(epsilon1(), 2)
    n = 2
    bad = 0
    for i in range(12):
        if v.is_zero():
            print('  reached zero')
            break
        kind = 'fs' if model_is_limit(v) else 'pred'
        model = to_d(v)
        print(f'  {i}: {kind:<4} {v!r}')
        if kind == 'fs':
            v2 = model_fs(v, n)
            want = D.fs(model, n)
        else:
            v2 = pred(v)
            want = D.pred(model)
            n += 1
        got = to_d(v2)
        if got != want:
            bad += 1
            print(f'      MODEL MISMATCH: model {want!r}, BVE {got!r}')
        v = v2
    print('  ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_decrease():
    print()
    print('every limit/successor move decreases the ordinal')
    terms = [epsilon1(), fs(epsilon1(), 2), fs(epsilon1(), 3),
             phi(0, epsilon1()), phi(1, epsilon1()),
             add(phi(0, ONE), ONE), phi(0, phi(0, ONE))]
    bad = 0
    for a in terms:
        if a.is_zero():
            continue
        b, _, kind = model_step(a, 2)
        ok = _cmp_v(b, a) < 0
        bad += not ok
        print(f'  {kind:<4} {a!r}  ->  {b!r}  {"OK" if ok else "FAIL"}')
    print('  ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_random():
    print()
    print('random terms: token round-trip, decrease, and oracle agreement')
    rng = random.Random(7)

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

    bad = 0
    checked = 0
    oracle = 0
    for _ in range(200):
        a = term(3)
        s = encode(a)
        if len(s) % 2 or any(s[i:i + 2] not in TOKENS
                              for i in range(0, len(s), 2)):
            bad += 1
            print(f'  BAD TOKENS {s!r}')
            continue
        if parse(s) != a:
            bad += 1
            print(f'  ROUND-TRIP FAIL {a!r}')
            continue
        checked += 1
        if a.is_zero():
            continue
        b, _, _ = model_step(a, 2)
        if _cmp_v(b, a) >= 0:
            bad += 1
            print(f'  NO DECREASE {a!r} -> {b!r}')
            continue
        if not (tower_fragment(a) and tower_fragment(b)):
            continue
        ma = to_d(a)
        if D.is_limit(ma):
            want = D.fs(ma, 2)
            got = to_d(b)
        else:
            want = D.pred(ma)
            got = to_d(b)
        if got != want:
            bad += 1
            print(f'  ORACLE FAIL {a!r} -> {b!r}')
            print(f'    want {want!r}')
            print(f'    got  {got!r}')
        else:
            oracle += 1
    print(f'  {checked} round-trips, {oracle} oracle checks, '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def trace(max_moves=6):
    """Print the first moves from epsilon_1; used by `python tools/eps1_bve.py trace`."""
    v = epsilon1()
    n = 3
    for i in range(max_moves):
        if v.is_zero():
            print(f'{i}: 0')
            break
        text = repr(v)
        if len(text) > 140:
            text = text[:137] + '...'
        kind = 'start' if i == 0 else ''
        print(f'{i}: {len(encode(v)) // 2:4d} tokens  {text}')
        v, n, kind = model_step(v, n)


def check_lengths():
    print()
    print('move counts on the common fragment (cap 5k)')
    bad = 0
    for k in range(0, 3):
        start = D.tower(k)
        for n in (1, 2):
            v = fs(epsilon1(), k)
            got_v, got_steps = hardy(v, n, cap=5_000)
            want_v, want_steps = D.hardy(start, n, cap=5_000)
            same = (got_v is None and want_v is None) or got_steps == want_steps
            bad += not same
            print(f'  member {k} n={n}: BVE {got_steps}'
                  f'{"+" if got_v is None else ""} vs model {want_steps}'
                  f'{"+" if want_v is None else ""}  {"OK" if same else "FAIL"}')
    return bad == 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'trace':
        trace()
        return 0
    ok = True
    ok = check_roundtrip() and ok
    ok = check_epsilon1_sequence() and ok
    ok = check_epsilon0_sequence() and ok
    ok = check_descent() and ok
    ok = check_decrease() and ok
    ok = check_random() and ok
    ok = check_lengths() and ok
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
