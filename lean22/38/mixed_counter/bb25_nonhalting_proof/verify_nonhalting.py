#!/usr/bin/env python3
"""Executable checks for the accompanying MATHEMATICAL nonhalting proof.

Machine: 1RB2LA0RB1LA3LB_1LA3LB1RA4RA---
This script is not a Lean/kernel verification and finite tests are not the proof.
The universal argument is in NONHALTING_PROOF.md.

Reset-word notation: V=22, 0=C=13, 1=C1=23; final P Q is implicit.
Left words for capacity() are physical-order: far left -> head, U/W/D.
Block configurations use nearest-to-head first on BOTH sides, as in Closed.lean.
Requires only Python 3.10+ standard library.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable

MACHINE = '1RB2LA0RB1LA3LB_1LA3LB1RA4RA---'
SEED8 = 'VVVVVV1011'
SEED12 = 'VVVVVVVVVVVVVVVV1VVVV1V1V10VVVV0101001010111111111'
Cfg = tuple[tuple[str, ...], str, tuple[str, ...]]
Raw = tuple[str, str, tuple[int, ...], tuple[int, ...]]

@dataclass(frozen=True)
class Stats:
    height: int
    debt: int
    promotions: int
    image: str

    @property
    def normalized(self) -> Fraction:
        if self.height >= 0:
            return Fraction(self.debt, 1 << self.height)
        return Fraction(self.debt * (1 << (-self.height)), 1)


def scan(word: str) -> Stats:
    """Debt transducer and the mixed-left-counter saturation image."""
    h = x = p = 0
    image: list[str] = []
    for a in word:
        if a == 'V':
            h += 1; x *= 2; image.append('V')
        elif a == '1':
            h += 1; x = 2*x + 2; image.append('V')
        elif a == '0':
            bit = 1 - (x % 2)
            image.append(str(bit)); p += bit
            h -= 1; x = x//2 + 3
        else:
            raise ValueError(f'Not a reset digit: {a!r}')
    return Stats(h, x, p, ''.join(image))


def trailing_ones(word: str) -> int:
    return len(word) - len(word.rstrip('1'))


def good(word: str) -> bool:
    s = scan(word)
    return (word.count('V') - word.count('0') - word.count('1') == 2
            and trailing_ones(word) >= 6
            and s.promotions >= 3
            and s.normalized <= Fraction(1, 256))


def cascade_capacity(word: str) -> int:
    """Checks EVERY increment precondition, not just the final capacity."""
    e = 0
    for i, a in enumerate(word):
        if a == 'V': e = 2*e + 1
        elif a == '1':
            if e < 1: raise ValueError(f'Cascade interrupted at digit {i}')
            e = 2*e - 1
        elif a == '0':
            if e < 6: raise ValueError(f'Cascade interrupted at digit {i}')
            e = (e-6)//2
        else: raise ValueError(a)
    return e


def reset_word(word: str) -> str:
    """Exact full reset return, under explicitly checked domain conditions."""
    if not word.endswith('1'):
        raise ValueError('This return lemma requires the last digit to be 1')
    s = scan(word)
    e = cascade_capacity(word)
    if s.height < 3 or e != (1 << s.height)-1-s.debt:
        raise ValueError('Height/capacity identity failed')
    if (e-1)//2 < 6:
        raise ValueError('Not enough cycles to normalize C G G')
    u = scan(word[:-1])
    n, d = s.height-3, u.debt-9
    if not (0 <= d < (1 << n)):
        raise ValueError('Successor does not have the claimed P Q tail')
    bits = ''.join('0' if (d >> i) & 1 else '1' for i in range(n))
    return u.image + bits


def capacity(left: Iterable[str]) -> int:
    c = 0
    for a in left:
        if a == 'U': c = 2*c+1
        elif a == 'W': c *= 2
        elif a == 'D': c //= 2
        else: raise ValueError(a)
    return c


def saturation_image(left: Iterable[str]) -> str:
    c = 0; out: list[str] = []
    for a in left:
        if a == 'D': out.append(str(c % 2)); c //= 2
        elif a == 'U': out.append('V'); c = 2*c+1
        elif a == 'W': out.append('V'); c *= 2
        else: raise ValueError(a)
    return ''.join(out)


def block_step(cfg: Cfg) -> Cfg:
    """Independent transcription of TM25.astep in the uploaded Closed.lean."""
    l, h, r = cfg
    if h == '<':
        if not l: return l, 'w', r
        a, t = l[0], l[1:]
        if a == 'W': return t, '<', ('V',)+r
        if a == 'U': return ('W',)+t, '>', r
        if a == 'D': return t, '<', ('0',)+r
    elif h == '>':
        if not r: return l, '<', ('P','Q')
        a, t = r[0], r[1:]
        if a == 'V': return ('U',)+l, '>', t
        if a == '0': return l, '<', ('1',)+t
        if a == '1': return ('D',)+l, '>', t
        if a == 'G': return l, '<', ('0',)+t
        if a == 'P': return l, 'w', t
        if a == 'S': return l, '<', ('Q',)+t
        if a == 'Q': return l, '<', ('P',)+t
    elif h == 'w':
        if not r: return l, 'b', ('G',)
        a, t = r[0], r[1:]
        if a == 'V': return ('U',)+l, 'w', t
        if a == '0': return l, '<', ('0','S')+t
        if a == '1': return l, '<', ('P','V')+t
        if a == 'G': return l, '<', ('0','Q')+t
        if a == 'P': return ('U',)+l, '>', t
        if a == 'S': return ('D',)+l, '>', t
        if a == 'Q': return l, '<', ('0',)+t
    elif h == 'b':
        if not l: raise RuntimeError('Proved left-end loop')
        a, t = l[0], l[1:]
        if a == 'U': return t, '<', ('0',)+r
        if a == 'W': return t, 'b', ('G',)+r
        if a == 'D': raise RuntimeError('HALT')
    raise ValueError(cfg)

TRANS = {
    ('A',0):(1,'R','B'), ('A',1):(2,'L','A'), ('A',2):(0,'R','B'),
    ('A',3):(1,'L','A'), ('A',4):(3,'L','B'), ('B',0):(1,'L','A'),
    ('B',1):(3,'L','B'), ('B',2):(1,'R','A'), ('B',3):(4,'R','A')}


def raw_step(c: Raw) -> Raw:
    q, d, l, r = c
    a = (l[0] if l else 0) if d == 'L' else (r[0] if r else 0)
    if (q,a) not in TRANS: raise RuntimeError('Raw TM halted')
    w, dd, qq = TRANS[q,a]
    if d == 'L':
        return (qq, dd, l[1:], (w,)+r) if dd == 'L' else (qq, dd, (w,)+l[1:], r)
    return (qq, dd, l, (w,)+r[1:]) if dd == 'L' else (qq, dd, (w,)+l, r[1:])


def trim(w: tuple[int, ...]) -> tuple[int, ...]:
    n = len(w)
    while n and w[n-1] == 0: n -= 1
    return w[:n]


def raw_key(c: Raw) -> tuple[str, tuple[int, ...], tuple[int, ...]]:
    q, d, l, r = c
    if d == 'L':
        r = ((l[0] if l else 0),)+r; l = l[1:]
    return q, trim(l), trim(r)


def concrete(c: Cfg) -> Raw:
    lc = {'U':(1,0), 'W':(1,1), 'D':(4,0)}
    rc = {'V':(2,2), '0':(1,3), '1':(2,3), 'G':(3,3),
          'P':(2,), 'Q':(1,), 'S':(3,)}
    l, h, r = c
    ll = tuple(z for a in l for z in lc[a])+(1,1)
    rr = tuple(z for a in r for z in rc[a])
    if h == 'w': return 'B','R',(0,)+ll,rr
    return ('B' if h == 'b' else 'A'), ('L' if h in ('<','b') else 'R'),ll,rr


def check_seed() -> None:
    c: Cfg = (('W',), '<', ('0',))
    raw: Raw = ('A','R',(),())
    for _ in range(21): raw = raw_step(raw)
    assert raw_key(raw) == raw_key(concrete(c))
    raw_count = 21
    for _ in range(504):
        nxt = block_step(c)
        for j in range(1, 33):
            raw = raw_step(raw)
            if raw_key(raw) == raw_key(concrete(nxt)):
                raw_count += j; break
        else: raise AssertionError('Block step disagrees with the raw TM')
        c = nxt
    assert c == ((), '<', tuple(SEED8)+('P','Q'))
    print(f'Raw TM and all 504 block steps agree; reset 8 reached after {raw_count} raw steps.')
    w = SEED8
    for i in range(8,12):
        w = reset_word(w)
        print(f'Exact checked return {i} -> {i+1}: word length {len(w)}.')
    assert w == SEED12 and good(w)
    s = scan(w)
    print(f'Seed 12: H={s.height}, x={s.debt}, p={s.promotions}, '
          f'trailing ones={trailing_ones(w)}, M={s.normalized}.')


def check_mixed_words(max_length: int = 7) -> None:
    sentinel = ('G','P','Q'); checked = 0
    for n in range(max_length+1):
        for w in product('UWD', repeat=n):
            cap = capacity(w)
            c: Cfg = (tuple(reversed(w)), '<', sentinel)
            for t in range(200000):
                if c[1] == '<' and not c[0]:
                    assert cap == 0
                    assert c[2] == tuple(saturation_image(w))+sentinel
                    break
                if c[1] == '>' and c[2] == sentinel:
                    assert cap > 0
                    out = tuple(reversed(c[0]))
                    assert capacity(out) == cap-1
                    assert saturation_image(out) == saturation_image(w)
                    break
                c = block_step(c)
            else: raise AssertionError('Mixed return test exceeded its bound')
            checked += 1
    print(f'Capacity / decrement / saturation-image checks: {checked} mixed left words.')


def check_arithmetic(max_length: int = 9, t_limit: int = 65536) -> None:
    checked = 0
    for n in range(max_length+1):
        for letters in product('V01', repeat=n):
            word = ''.join(letters); a = scan(word); b = scan(a.image)
            assert b.height == a.height + 2*a.promotions
            if a.promotions == 0:
                assert b.debt == 0 and a.debt % 2 == 0
            else:
                assert b.debt <= (4**(a.promotions-1))*a.debt
            checked += 1
    vals = [Fraction(2)]
    for d in range(1,t_limit):
        v = 1+vals[d//2]/2 if d%2 == 0 else 6+2*vals[d//2]
        vals.append(v)
        assert v <= 8*d+2
    print(f'Image-lemma checks: {checked} words; tail-cost bound checks: {t_limit} integers.')


def check_orbit(last_reset: int) -> None:
    w = SEED12
    for i in range(12,last_reset+1):
        assert good(w)
        a = scan(w)
        cascade_capacity(w)
        print(f'Reset {i}: len={len(w)}, V={w.count("V")}, '
              f'0={w.count("0")}, 1={w.count("1")}, H={a.height}, '
              f'x_bits={a.debt.bit_length()}, p={a.promotions}, '
              f'last_ones={trailing_ones(w)}')
        nxt = reset_word(w); b = scan(nxt)
        assert good(nxt)
        assert b.normalized <= Fraction(3,8)*a.normalized
        w = nxt
    print('All requested finite checks passed. The infinite conclusion uses the written induction.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--last-reset', type=int, default=22)
    parser.add_argument('--skip-exhaustive', action='store_true')
    args = parser.parse_args()
    if args.last_reset < 12: parser.error('--last-reset must be at least 12')
    print(MACHINE)
    check_seed()
    if not args.skip_exhaustive:
        check_mixed_words(); check_arithmetic()
    check_orbit(args.last_reset)

if __name__ == '__main__': main()
