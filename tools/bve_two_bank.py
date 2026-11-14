"""Two-bank rBVE: the recommended 2-symbol tape layout for the BVE descent.

Single-field reversed postfix makes the right spine a prefix, but a coefficient
deletion is a middle deletion: the last principal's exponent is followed by the
exponents of earlier principals.  Split the term into two banks instead:

    header bank H:  f1 op1  f2 op2  ...  fk opk
    exponent bank E: postfix(a1) 000 postfix(a2) 000 ... 000 postfix(ak)

  * H is the right spine, in order.  `fi` is a one-cell duplicate flag: 1 iff
    this principal is the same ordinal as the previous one (coefficient > 1).
  * E holds the exponents in the SAME order as H, each in ordinary postfix
    (`left right op`), so the last exponent's root is the LAST token of E.
  * The last principal is therefore the last header and the last exponent.
    Popping one coefficient is a suffix truncation in both banks, not a middle
    shift.

Token framing is the four-cell code from bve_tape.py:

    1001 = 0      1011 = 1      1101 = phi_0      1111 = phi_1

Every token starts and ends with 1, so `000` cannot occur inside a bank.  One
`000` separates H from E and separates the exponent blocks; `0000` terminates
the whole term field.  A complete tape is

    0000 [H 000 E] 0000 [work/cursor stack] 0000 [index] 0000

The scanner/checks below only validate the layout and suffix access.  They do
not claim a transition table or a rewrite engine.
"""

import random
import sys

sys.path.insert(0, 'tools')

import eps1_bve as B
from eps1_bve import V, ZERO, ONE, phi, add
from bve_tape import DELIM, TOK_ZERO, TOK_ONE, TOK_OP, OP_OF_TOK

FIELD = '0000'
HDR_OP = {i: TOK_OP[i] for i in TOK_OP}


def postfix(v):
    """Ordinary postfix: left right op, so the root is the last token."""
    if v.is_zero():
        return TOK_ZERO
    if v == ONE:
        return TOK_ONE
    p = v.terms[0]
    rest = V(v.terms[1:])
    return postfix(p.a) + postfix(rest) + HDR_OP[p.i]


def parse_postfix(s):
    stack = []
    pos = 0
    while pos < len(s):
        tok = s[pos:pos + 4]
        if tok == TOK_ZERO:
            stack.append(ZERO)
        elif tok == TOK_ONE:
            stack.append(ONE)
        elif tok in OP_OF_TOK:
            if len(stack) < 2:
                raise ValueError(f'missing operands at {pos}')
            right = stack.pop()
            left = stack.pop()
            stack.append(add(phi(OP_OF_TOK[tok], left), right))
        else:
            raise ValueError(f'bad postfix token {tok!r} at {pos}')
        pos += 4
    if len(stack) != 1:
        raise ValueError(f'postfix stack has {len(stack)} terms')
    return stack[0]


def header(p, dup):
    return ('1' if dup else '0') + HDR_OP[p.i]


def banks(v):
    """Return (H, E) for a term; H empty means zero."""
    if v.is_zero():
        return '', ''
    hs = []
    prev = None
    for p in v.terms:
        hs.append(header(p, prev == p))
        prev = p
    h = ''.join(hs)
    e = DELIM.join(postfix(p.a) for p in v.terms)
    return h, e


def to_tape(v, work='', index=''):
    h, e = banks(v)
    body = h + DELIM + e if h else TOK_ZERO + DELIM
    return FIELD + body + FIELD + work + FIELD + index + FIELD


def split(tape):
    if not tape.startswith(FIELD):
        raise ValueError('tape must start with the four-zero field marker')
    start = len(FIELD)
    h_end = tape.find(DELIM, start)
    if h_end < 0:
        raise ValueError('missing H/E separator')
    h = tape[start:h_end]
    if h == TOK_ZERO:
        return h, ''
    # A suffix-truncated H leaves a longer zero run before E; E starts at the
    # first token after that run.  Nonzero terms always have at least one
    # exponent token; the zero term is handled above.
    e_start = h_end + len(DELIM)
    while e_start < len(tape) and tape[e_start] == '0':
        e_start += 1
    e_end = tape.find(FIELD, e_start)
    if e_end < 0:
        raise ValueError('unterminated term field')
    return h, tape[e_start:e_end]


def from_tape(tape):
    h, e = split(tape)
    if h == TOK_ZERO:
        return ZERO
    if len(h) % 5:
        raise ValueError(f'header bank length {len(h)} is not a multiple of 5')
    ops = []
    for pos in range(0, len(h), 5):
        flag = h[pos]
        tok = h[pos + 1:pos + 5]
        if flag not in '01' or tok not in OP_OF_TOK:
            raise ValueError(f'bad header at {pos}: {h[pos:pos + 5]!r}')
        ops.append((OP_OF_TOK[tok], flag == '1'))
    exps = e.split(DELIM) if e else []
    if len(exps) != len(ops):
        raise ValueError(f'{len(ops)} headers but {len(exps)} exponents')
    out = ZERO
    for (i, _dup), es in zip(ops, exps):
        out = add(out, phi(i, parse_postfix(es)))
    return out


def header_scan(tape):
    """Return [(index, duplicate_flag, cell)] for H, left to right."""
    h, _e = split(tape)
    if h == TOK_ZERO:
        return []
    if len(h) % 5:
        raise ValueError('bad header bank')
    out = []
    for pos in range(0, len(h), 5):
        out.append((OP_OF_TOK[h[pos + 1:pos + 5]], h[pos] == '1',
                    len(FIELD) + pos))
    return out


def truncate_last(tape):
    """The tape after deleting the last header and its exponent suffix.

    This is what the predecessor arm does when the last duplicate flag is 1.
    It is a suffix cut in both banks; the cursor only has to zero the last
    header (five cells) and the last exponent block, not shift anything.
    """
    h, e = split(tape)
    if not h or h == TOK_ZERO:
        raise ValueError('zero term has no last principal')
    h2 = h[:-5]
    cut = e.rfind(DELIM)
    e2 = '' if cut < 0 else e[:cut]
    body = (h2 + DELIM + e2) if h2 else (TOK_ZERO + DELIM)
    return FIELD + body + FIELD


def last_exponent(tape):
    """Return (start_cell, text) of the last exponent in E."""
    h, e = split(tape)
    if not h or h == TOK_ZERO:
        raise ValueError('zero term has no exponent')
    e_start = len(FIELD) + len(h) + len(DELIM)
    cut = e.rfind(DELIM)
    if cut < 0:
        return e_start, e
    return e_start + cut + len(DELIM), e[cut + len(DELIM):]


def check():
    rng = random.Random(19)

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

    print('two-bank rBVE: headers, suffix exponents, duplicate flags')
    terms = [ZERO, ONE, phi(0, ZERO), phi(1, ZERO),
             add(phi(0, ONE), ONE), phi(1, ONE), phi(0, phi(0, ONE)),
             add(ONE, ONE), add(phi(0, add(ONE, ONE)), ONE)]
    terms += [term(3) for _ in range(120)]
    bad = 0
    for v in terms:
        tape = to_tape(v)
        if from_tape(tape) != v:
            bad += 1
            print(f'  ROUND-TRIP FAIL: {v!r}')
            continue
        hs = header_scan(tape)
        want = v.terms
        if len(hs) != len(want) or any(i != p.i for (i, _, _), p in zip(hs, want)):
            bad += 1
            print(f'  HEADER FAIL: {v!r}')
            continue
        if v.is_zero():
            if hs:
                bad += 1
                print('  ZERO HEADER FAIL')
            continue
        start, text = last_exponent(tape)
        if text != postfix(want[-1].a):
            bad += 1
            print(f'  SUFFIX FAIL: {v!r}: {text!r} != {postfix(want[-1].a)!r}')
            continue
        if tape[start:start + len(text)] != text:
            bad += 1
            print(f'  SUFFIX OFFSET FAIL: {v!r}')
            continue
        if len(want) >= 2 and want[-1] == want[-2]:
            cut_term = V(want[:-1])
            if from_tape(truncate_last(tape)) != cut_term:
                bad += 1
                print(f'  SUFFIX POP FAIL: {v!r} -> {cut_term!r}')
    print(f'  {len(terms)} terms: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def example():
    print('example: epsilon_1 = phi_1(1)')
    v = B.epsilon1()
    h, e = banks(v)
    print(f'  term       {v!r}')
    print(f'  H          {h}   ({len(h) // 5} header)')
    print(f'  E          {e}')
    print(f'  tape       {to_tape(v)}')
    print(f'  last exp   {last_exponent(to_tape(v))[1]}')
    print()
    print('example: w + 1 (two headers, last exponent is 0)')
    v = add(phi(0, ONE), ONE)
    print(f'  term       {v!r}')
    print(f'  H          {banks(v)[0]}')
    print(f'  E          {banks(v)[1]}')
    print(f'  headers    {header_scan(to_tape(v))}')


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
