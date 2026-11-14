"""A 2-symbol tape layout for the binary Veblen tree, and a spine scanner.

The BVE term is a binary tree.  Ordinary postfix is `left right op`; that makes
the right spine hard to find because the last additive principal is buried
before the root operator.  Store the tree in REVERSED postfix instead:

    node  =  op  right  left

For a term in Veblen normal form the principal terms are the right spine, so
their headers are a CONTIGUOUS PREFIX of the term field:

    op1 right(op2 right(op3 ... zero) ...) exponent(op1) exponent(op2) ...

The right-spine cursor therefore walks token-to-token, never over an exponent
subtree.  This module fixes the tape codec for that layout and checks the
prefix property; it is not yet the full rewrite machine.

Token framing.  Four BVE tokens need four codes, and the field delimiter must
not collide with a token.  Use four cells per token:

    1001 = 0       1011 = 1       1101 = phi_0       1111 = phi_1

Every token starts and ends with 1, and no token contains `000`; token
concatenation cannot create `000` either.  `000` is therefore a field
delimiter.  A complete tape is

    000 [rBVE term field] 000 [cursor/work field] 000 [index field] 000

The work and index fields are reserved here; the scanner only reads the term
field.  A field is copied with `field()` and its start offset is 3.
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, P, ZERO, ONE, phi, add

DELIM = '000'
TOK_ZERO = '1001'
TOK_ONE = '1011'
TOK_OP = {0: '1101', 1: '1111'}
OP_OF_TOK = {v: k for k, v in TOK_OP.items()}
ALL_TOKENS = (TOK_ZERO, TOK_ONE, TOK_OP[0], TOK_OP[1])


def enc(v):
    """Encode a Veblen term in reversed postfix.

    Every nonzero principal is a node, including 1 = phi_0(0), so the right
    spine is a uniform sequence of op tokens.  The BVE leaf `01` is not needed
    on tape; `TOK_ONE` is kept only for decoding a hand-written field.
    """
    if v.is_zero():
        return TOK_ZERO
    p = v.terms[0]
    rest = V(v.terms[1:])
    return TOK_OP[p.i] + enc(rest) + enc(p.a)


def dec(s, pos=0):
    """Decode a reversed-postfix term; returns (term, next_offset)."""
    if len(s) - pos < 4:
        raise ValueError(f'truncated token at offset {pos}')
    tok = s[pos:pos + 4]
    if tok == TOK_ZERO:
        return ZERO, pos + 4
    if tok == TOK_ONE:
        return ONE, pos + 4
    if tok not in OP_OF_TOK:
        raise ValueError(f'bad token {tok!r} at offset {pos}')
    i = OP_OF_TOK[tok]
    right, pos = dec(s, pos + 4)
    left, pos = dec(s, pos)
    return add(phi(i, left), right), pos


def field(tape):
    """Return the term field of a complete tape string."""
    if not tape.startswith(DELIM):
        raise ValueError('tape must start with a field delimiter')
    end = tape.find(DELIM, len(DELIM))
    if end < 0:
        raise ValueError('unterminated term field')
    return tape[len(DELIM):end]


def to_tape(v, work='', index=''):
    """Build the full tape around a term field; work/index are raw fields."""
    return DELIM + enc(v) + DELIM + work + DELIM + index + DELIM


def from_tape(tape):
    """Decode the term field, rejecting trailing cells or embedded delimiters."""
    s = field(tape)
    v, pos = dec(s)
    if pos != len(s):
        raise ValueError(f'term field has {len(s) - pos} trailing cells')
    return v


def headers(tape):
    """Scan the right spine.

    Returns (headers, tail, exponent_start), where each header is (index, cell)
    and tail is 'zero' or 'one'.  `exponent_start` is the first cell of the
    last principal's exponent.  All offsets are absolute tape offsets.
    """
    if not tape.startswith(DELIM):
        raise ValueError('tape must start with a field delimiter')
    pos = len(DELIM)
    out = []
    while True:
        tok = tape[pos:pos + 4]
        if tok == TOK_ZERO:
            return out, 'zero', pos + 4
        if tok == TOK_ONE:
            return out, 'one', pos + 4
        if tok in OP_OF_TOK:
            out.append((OP_OF_TOK[tok], pos))
            pos += 4
            continue
        raise ValueError(f'bad spine token {tok!r} at offset {pos}')


def check():
    rng = random.Random(11)

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

    print('rBVE tape codec: token framing and right-spine prefix')
    terms = [ZERO, ONE, phi(0, ZERO), phi(1, ZERO),
             add(phi(0, ONE), ONE), phi(1, ONE), phi(0, phi(0, ONE))]
    terms += [term(3) for _ in range(100)]
    bad = 0
    for v in terms:
        s = enc(v)
        if DELIM in s:
            bad += 1
            print(f'  DELIMITER COLLISION: {v!r}')
            continue
        if from_tape(to_tape(v)) != v:
            bad += 1
            print(f'  ROUND-TRIP FAIL: {v!r}')
            continue
        hs, tail, exp_at = headers(to_tape(v))
        want = v.terms
        if len(hs) != len(want) or any(i != p.i for (i, _), p in zip(hs, want)):
            bad += 1
            print(f'  SPINE FAIL: {v!r}: {hs} vs {want}')
            continue
        if v.is_zero():
            if hs or tail != 'zero':
                bad += 1
                print(f'  ZERO SPINE FAIL: {hs} {tail}')
            continue
        last = want[-1]
        if tail != 'zero':
            bad += 1
            print(f'  TAIL FAIL: {v!r} -> {tail}')
            continue
        if to_tape(v)[exp_at:exp_at + len(enc(last.a))] != enc(last.a):
            bad += 1
            print(f'  EXPONENT OFFSET FAIL: {v!r}')
    print(f'  {len(terms)} terms: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    print('example: epsilon_1 = 01 00 11')
    v = B.epsilon1()
    print(f'  term       {v!r}')
    print(f'  field      {enc(v)}')
    print(f'  tape       {to_tape(v)}')
    hs, tail, exp_at = headers(to_tape(v))
    print(f'  spine      {hs}')
    print(f'  tail       {tail}')
    print(f'  exponent   {to_tape(v)[exp_at:]}')
    print()
    print('example: w + 1 (two spine headers, coefficient 1)')
    v = add(phi(0, ONE), ONE)
    hs, tail, exp_at = headers(to_tape(v))
    print(f'  term       {v!r}')
    print(f'  spine      {hs}')
    print(f'  tail       {tail}')
    print(f'  exponent   {to_tape(v)[exp_at:]}')


def main():
    ok = check()
    if ok:
        print()
        example()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
