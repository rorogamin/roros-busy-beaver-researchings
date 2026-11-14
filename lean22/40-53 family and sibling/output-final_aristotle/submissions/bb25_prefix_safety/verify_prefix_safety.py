#!/usr/bin/env python3
"""Reproducible checks for the 3RA/2LA prefix-safety proof.

The universal proof is in PROOF.md. This program is an independent finite
sanity check, not a replacement for that proof or a Lean kernel certificate.
Stacks are bottom-first, and exclude the permanent left-end block L.
Only Python's standard library is required. The three reference_tools files
are copied unchanged from the user's supplied Aristotle archive.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
import random
import sys
from typing import Iterable

Stack = tuple[str, ...]


def value(s: Iterable[str]) -> int:
    a = 0
    for ch in s:
        if ch == 'Z': a = 2*a + 1
        elif ch == 'X': a *= 2
        elif ch == 'W': a //= 2
        else: raise ValueError(ch)
    return a


def decode(s: Iterable[str]) -> str:
    """The paired decoder P; raises ValueError for an unmatched W."""
    active: list[str] = []
    word: list[str] = []
    for ch in s:
        if ch in ('X', 'Z'):
            active.append(ch)
            word.append('Y')
        elif ch == 'W':
            if not active: raise ValueError('unmatched W')
            word.append('V' if active.pop() == 'Z' else 'X')
        else: raise ValueError(ch)
    return ''.join(word)


def adjusted_step(a: int, ch: str) -> int:
    if ch == 'Y': return 2*a + 1
    if ch == 'V': return 2*a
    if ch == 'X': return a//2 - 1
    raise ValueError(ch)


def adjusted(word: str, start: int = 0) -> int:
    a = start
    for ch in word: a = adjusted_step(a, ch)
    return a


def good(s: Stack) -> bool:
    """All prefixes u satisfy rho(P(u)) >= value(u), and W is matched."""
    active: list[str] = []
    a = b = 0
    for ch in s:
        if ch in ('X', 'Z'):
            active.append(ch)
            a = 2*a + (ch == 'Z')
            b = 2*b + 1
        elif ch == 'W':
            if not active: return False
            label = 'V' if active.pop() == 'Z' else 'X'
            a //= 2
            b = adjusted_step(b, label)
        else: return False
        if b < a: return False
    return True


def dec(s: Stack) -> Stack:
    """Decrement only the final unmatched bits; matched pairs are frozen."""
    active: list[int] = []
    for i, ch in enumerate(s):
        if ch in ('X', 'Z'): active.append(i)
        elif ch == 'W':
            if not active: raise ValueError('unmatched W')
            active.pop()
        else: raise ValueError(ch)
    out = list(s)
    for i in reversed(active):
        if out[i] == 'Z':
            out[i] = 'X'
            return tuple(out)
        out[i] = 'Z'
    raise ValueError('zero counter')


def reset_paid(word: str) -> Stack:
    """Left-stack effect of a clean reset with final pending debt paid."""
    s: Stack = ()
    for ch in word:
        if ch == 'Y': s += ('Z',)
        elif ch == 'V': s += ('X',)
        elif ch == 'X':
            if value(s) < 2: raise ValueError('unclean reset')
            s = dec(s + ('W',))
        else: raise ValueError(ch)
        assert good(s), ('reset preservation', word, s)
    assert value(s) == adjusted(word)
    return s


def transpose_word(word: str, a: int = 0) -> str:
    out: list[str] = []
    for ch in word:
        out.append('Y' if ch in ('Y', 'V') else 'V' if a % 2 else 'X')
        a = adjusted_step(a, ch)
    return ''.join(out)


def strong(s: Stack) -> bool:
    return good(s) and adjusted(decode(s)) + 2 >= 4*(value(s) + 1)


def drain_to_B(s: Stack) -> Stack:
    """Starts at A> $; returns the next B1 boundary."""
    assert strong(s)
    while value(s):
        old = value(s)
        s = dec(s) + ('W',)
        assert value(s) == (old - 1)//2
        assert strong(s), ('drain', s)
    word = decode(s) + 'V'
    assert adjusted(word) >= 4
    out = reset_paid(word)
    assert good(out) and value(out) >= 1
    return out


@dataclass(frozen=True)
class Return:
    kind: str                 # 'B' or 'spinout'
    stack: Stack = ()
    branch: str = ''


def successor(member: str, s: Stack) -> Return:
    """The constructive checkpoint-return lemma from PROOF.md."""
    if member not in ('3RA', '2LA'): raise ValueError('proof covers 3RA and 2LA only')
    if not good(s) or value(s) < 1: raise ValueError('not a safe B boundary')
    k = 0
    while s[-1] == 'X':
        s = s[:-1]
        k += 1
    top, core = s[-1], s[:-1]
    assert top in ('Z', 'W')
    r = k + 1
    if top == 'Z':
        required, push, branch = 2, 'W', 'Z'
    elif member == '3RA':
        assert value(core) >= 2
        required, push, branch = 4, 'W', 'W-3RA'
    else:
        assert value(core) >= 2
        required, push, branch = 3, 'Z', 'W-2LA'
    v = value(core)
    for _ in range(min(v, required)): core = dec(core)
    assert good(core)
    if v >= required:
        core += (push,)
        assert good(core)
        core += ('Z',)*r + ('W',)
        assert strong(core)
        return Return('B', drain_to_B(core), branch+'-direct')

    # All F/G blocks have already been erased; the residual symbol is b.
    assert value(core) == 0
    if top == 'Z': b = 'X' if v == 0 else 'V'
    elif member == '3RA': b = 'X' if v == 2 else 'V'
    else: b = 'Y'
    u = decode(core)
    word = u + b + 'Y'*r + 'V'
    if adjusted(word) >= 1:
        out = reset_paid(word)
        return Return('B', out, branch+'-early-clean')

    assert b == 'X' and adjusted(u) in (0, 1)
    if not u:
        return Return('spinout', branch=branch+'-left-XY')

    # The one exceptional reset, followed by an odd-terminal clean reset.
    t = reset_paid(u)
    assert value(t) in (0, 1)
    assert decode(t) == transpose_word(u)
    t += ('W',)
    assert value(t) == 0 and good(t)
    odd_word = decode(t) + 'Y'*(r+1)
    t = reset_paid(odd_word) + ('W',)
    assert strong(t)
    return Return('B', drain_to_B(t), branch+'-early-exceptional')


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-length', type=int, default=10)
    p.add_argument('--random', type=int, default=200)
    p.add_argument('--reference-limit', type=int, default=10000)
    p.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = p.parse_args()
    if not 1 <= args.max_length <= 14: p.error('max-length must be in 1..14')
    if args.random < 0: p.error('random must be nonnegative')
    sys.path.insert(0, str(Path(__file__).parent/'reference_tools'))
    import blocksim as ref
    import sim as base

    def ref_return(member: str, s: Stack) -> tuple[str, Stack, int]:
        lt, st, rt = list(reversed(s))+['L'], 'B', ['Y', 'R1']
        for i in range(args.reference_limit):
            # Denotational XY spinout criterion, allowing an internal P2.
            if st == 'L' and lt == ['L']:
                raw = ref.denote(lt, st, rt)[3]
                if raw[:4] == [1, 1, 2, 2]: return 'spinout', (), i
            if i and st == 'B' and rt == ['Y', 'R1']:
                return 'B', tuple(reversed(lt[:-1])), i
            stride = ref.stride(lt) if st == 'L' else None
            if stride is not None: lt, _ = stride; st = 'R'
            else: lt, st, rt, _ = ref.bstep(member, lt, st, rt)
        raise AssertionError(('reference limit', member, s))

    counts: Counter[str] = Counter()
    branches: Counter[str] = Counter()
    for n in range(1, args.max_length+1):
        for s in product('XZW', repeat=n):
            try: word = decode(s)
            except ValueError: continue
            if value(s) > 0:
                t = dec(s)
                reference = ref.stride(list(reversed(s))+['L'])
                assert reference is not None
                assert t == tuple(reversed(reference[0][:-1]))
                assert decode(t) == word
                assert all(value(t[:j]) <= value(s[:j]) for j in range(n+1))
                counts['admissible_decrement_checks'] += 1
            if not good(s) or value(s) < 1: continue
            counts['safe_initial_stacks'] += 1
            for member in ('3RA', '2LA'):
                answer = successor(member, s)
                rk, rs, steps = ref_return(member, s)
                assert (answer.kind, answer.stack) == (rk, rs), (member, s, answer, rk, rs)
                counts['reference_return_checks'] += 1
                branches[member+':'+answer.branch] += 1
        print('checked stack length', n, dict(counts), flush=True)

    rng = random.Random(20260916)
    for _ in range(args.random):
        s: Stack = ()
        for _ in range(rng.randrange(20, 100)):
            if value(s) >= 2 and rng.random() < .4:
                s = dec(dec(s)) + ('W',)
            else:
                s += (rng.choice(('X', 'Z')),)
            assert good(s)
        if value(s) == 0: s += ('Z',)
        for member in ('3RA', '2LA'):
            answer = successor(member, s)
            rk, rs, _ = ref_return(member, s)
            assert (answer.kind, answer.stack) == (rk, rs)
            counts['random_reference_return_checks'] += 1

    # Independently replay the finite seed and the spinout in the base TM.
    machine = base.machine(None)  # B4 is deliberately undefined: it is not used.
    c = ([], 'A', 'R', [])
    for _ in range(156):
        c = base.step(machine, c)
        assert c is not None
    seed = ('Z', 'Z', 'Z', 'X', 'X', 'X')
    assert c == ref.denote(list(reversed(seed))+['L'], 'B', ['Y', 'R1'])
    assert good(seed) and value(seed) == 56 and adjusted(decode(seed)) == 63
    for suffix in ([], [4, 4], [1, 3, 4, 0]):
        c = ([1, 1], 'A', 'L', [1, 1, 2, 2]+suffix)
        for _ in range(9): c = base.step(machine, c)
        assert c == ([1, 1], 'A', 'L', [1, 1, 2, 2, 2]+suffix)
    result = {
        'status': 'all finite checks passed',
        'not_a_Lean_certificate': True,
        'max_exhaustive_stack_length': args.max_length,
        'random_seed': 20260916,
        'counts': dict(counts), 'branches': dict(branches),
        'blank_tape_seed_base_steps': 156,
        'seed_stack_bottom_first': ''.join(seed),
        'seed_counter': 56, 'seed_decoded_counter': 63,
        'left_XY_spinout_period': 9,
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
