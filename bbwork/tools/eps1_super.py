"""SUPER model layer: the eps_1 descent carried by ONE self-rewriting string.

This is the first earned layer of the <=40-state construction (EPS1_SUPER.md).
The design of record carries (p, chain, n) as three tape fields and its fs
phase alone costs ~27 states, so 40 total was out of reach by re-cut.  The
super representation compresses to a single evolving object on the tape, so
the index n -- the third growing field -- disappears as a MACHINE field:

  * the seed eps_1[n] is written at start by the setup (a fixed depth-n
    unroll is a blank-tape startup artifact of the run, not a state);
  * the descent itself runs with the fs parameter fixed at the seed (the
    variant recorded below), so nothing on the tape has to track a bumping
    index during the descent.

The encoding v1 (a single 0/1 string, left-to-right):

    [1-mark]*p  0  [atom-flag 1?] 0  E0 E1 ... Em-1  [0] [0..0 padding]

    entry(c >= 1) = 1*(bitlen(c)+1) + 0 + bin(c) MSB-first  (self-delimiting:
        the run of 1s before the 0 gives bitlen(c), then exactly that many
        bits follow; no separator needed between entries)
    chain end     = the first 0 not consumed by an entry's bit field (two
        blanks total when the last entry ends in 0)
    atom flag     = the bottom is eps_0 (flag 1, empty entry list) or eps_0+1
        (flag 1, single entry 1); flag 0 with entries [c0, ...] is the plain
        NUM-bottom chain.  The flag is needed because eps_0 is not a numeral.

Invariant used by the codec: top-1 entries are normalised into p (the same
normalise() rule as eps1_chain), so [ATOM,1] never appears on tape, and the
bottom is stored canonically as NUM (or the atom flag).

What IS checked here:

  * codec round-trip: decode(encode(p, chain)) == the canonical form of
    (p, chain), exactly;
  * every super step is faithful to eps1_chain's step with the fixed
    seed as the parameter (the tape layer computes the chain step's
    result and kind exactly), on a random battery; and the free,
    parameter-free branch (successor at p == 0) matches eps1_descent
    exactly: D.pred of the previous value;
  * tape layer == chain layer: a full run seeded from eps_1[n] on the tape
    takes exactly the same number of moves as the same fixed-parameter run
    at the chain level;
  * measured record: the fixed-parameter descent lengths recorded next to
    the Hardy (bumping-index) counts, with NO bound claim made.

What is NOT done here, honestly (the ledger in EPS1_SUPER.md): no 2-symbol
table, no state count, no local (head-stepping) realization of the moves,
no f_{eps_1}(n) step-bound argument.  This module is the model bridge only.

Run: python tools/eps1_super.py    (expect ALL OK)
"""

import sys
import random

sys.path.insert(0, 'tools')

import eps1_chain as C
import eps1_descent as D
from eps1_chain import NUM, ATOM, ATOM1, full, chain_of, is_succ
from eps1_descent import Ord, ZERO


# ------------------------------------------------------------------- codec

def _entry(c):
    assert c >= 1, 'entries are numerals >= 1 (the atom lives in the flag)'
    bits = bin(c)[2:]
    return '1' * (len(bits) + 1) + '0' + bits


def encode(p, chain):
    """(p, chain) -> tape as a 0/1 string (the only machine object)."""
    chain = list(chain)
    while len(chain) > 1 and isinstance(chain[-1], int) and chain[-1] == 1:
        chain.pop()
        p += 1
    flag = 0
    entries = []
    if chain:
        b0 = chain[0]
        if b0 == ATOM:              # the atom IS e_0+1 in this project
            flag, entries = 1, list(chain[1:])
        elif b0 == ATOM1:           # e_0+2: one more than the atom
            flag, entries = 2, list(chain[1:])
        elif isinstance(b0, Ord):
            entries = [b0.terms[0][1]] + list(chain[1:])
        else:
            entries = list(chain)
    body = ''.join(_entry(c) for c in entries)
    frame = '' if flag == 0 else '10' if flag == 1 else '110'
    parts = ['1' * p, '0', frame, '0', body, '00']
    return ''.join(parts)


def decode(tape):
    """Tape -> (p, chain); raises on any non-well-formed tape."""
    i, L = 0, len(tape)
    p = 0
    while i < L and tape[i] == '1':
        p += 1
        i += 1
    if i >= L or tape[i] != '0':
        raise ValueError(f'no p separator at {i}')
    i += 1
    if i >= L or tape[i] not in '01':
        raise ValueError(f'bad flag frame at {i}')
    if tape[i] == '0':
        flag = 0
        i += 1                      # the unconditional frame separator
    else:
        ones = 0
        while i < L and tape[i] == '1':
            ones += 1
            i += 1
        if ones > 2:
            raise ValueError(f'flag frame run longer than 2 at {i}')
        flag = ones                 # 1 = the atom, 2 = the atom + 1
        if i >= L or tape[i] != '0':
            raise ValueError(f'no flag separator at {i}')
        i += 1
        if i >= L or tape[i] != '0':
            raise ValueError(f'no frame separator at {i}')
        i += 1
    entries = []
    while i < L and tape[i] == '1':
        k = 0
        j = i
        while j < L and tape[j] == '1':
            k += 1
            j += 1
        k -= 1                                  # the 0 that closes the run
        j += 1                                  # skip that 0
        if k < 1:
            raise ValueError(f'degenerate entry at {i}')
        if j + k > L:
            raise ValueError(f'truncated entry at {i}')
        entries.append(int(tape[j:j + k], 2))
        i = j + k
    if i + 1 >= L or tape[i + 1] != '0':
        raise ValueError(f'no chain end at {i}')
    i += 2                                      # the chain-end 00
    if i < L and any(tape[t] != '0' for t in range(i, L)):
        raise ValueError('nonzero tail after the chain')
    if flag == 1:
        return p, [ATOM] + entries
    if flag == 2:
        return p, [ATOM1] + entries
    if not entries:
        return p, []
    return p, [NUM(entries[0])] + entries[1:]


# ------------------------------------------------------------------- canon

def canon(p, chain):
    """The codec's canonical form, rebuilt independently of encode()."""
    p, chain = _norm(p, chain)
    if chain and isinstance(chain[0], int):
        chain = [NUM(chain[0])] + list(chain[1:])
    return p, chain


# -------------------------------------------------------------------- moves

class Halt(Exception):
    pass


def super_step(tape, seed):
    """One fixed-parameter move ON TAPE.  Returns (tape, kind)."""
    p, chain = decode(tape)
    if not chain:
        raise Halt
    p2, c2, _n, kind = C.step(p, chain, seed)   # the fixed-parameter variant
    return encode(p2, c2), kind


def super_run(tape, seed, cap=200000):
    """The fixed-parameter descent on tape.  Returns (moves, kind_counts)."""
    moves = 0
    kinds = {'pred': 0, 'fs': 0}
    while True:
        try:
            tape, kind = super_step(tape, seed)
        except Halt:
            return moves, kinds
        kinds[kind] += 1
        moves += 1
        if moves > cap:
            return None, kinds


def seed_tape(n):
    """The blank-tape startup artifact: the setup writes eps_1[n]."""
    p, c = chain_of(D.tower(n))
    return encode(p, c)


# ------------------------------------------------------------------- checks

def _norm(p, chain):
    chain = list(chain)
    while len(chain) > 1 and isinstance(chain[-1], int) and chain[-1] == 1:
        chain.pop()
        p += 1
    return p, chain


def check_codec(trials=300, seed=5):
    print('codec round-trip: decode(encode(p, chain)) == canonical (p, chain)')
    rng = random.Random(seed)
    bad = 0
    for i in range(trials):
        if i % 5 == 0:                          # atom-bottom battery
            p, c = chain_of(D.tower(rng.randint(1, 3)))
        else:                                   # plain NUM-bottom chains
            p = rng.randint(0, 2)
            c = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                                        for _ in range(rng.randint(1, 3))]
        p, c = _norm(p, c)
        tp = encode(p, c)
        try:
            got = decode(tp)
        except ValueError as exc:
            bad += 1
            print(f'  DECODE FAIL p={p} chain={c!r} tape={tp!r}: {exc}')
            continue
        want = canon(p, list(c))
        if got != want:
            bad += 1
            print(f'  MISMATCH p={p} chain={c!r}: decoded {got!r} vs {want!r}')
    print(f'  {trials} round-trips: ' + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def check_moves(trials=200, seed=9, moves=4):
    print('fixed-parameter moves against eps1_descent, decoded after each')
    rng = random.Random(seed)
    bad = 0
    for t in range(trials):
        sd = rng.randint(1, 3)
        if t % 4 == 0:                          # atom bottoms from the towers
            p, c = chain_of(D.tower(sd))
        else:
            p = rng.randint(0, 2)
            c = [rng.choice([2, 3])] + [rng.choice([1, 1, 2, 3])
                                        for _ in range(rng.randint(1, 3))]
        p, c = _norm(p, c)
        V = full(p, c)
        tape = encode(p, c)
        for _ in range(moves):
            if V.is_zero():
                break
            try:
                tape, kind = super_step(tape, sd)
            except Halt:
                bad += 1
                print(f'  HALT TOO EARLY at p={p} chain={c!r} seed={sd}')
                break
            p3, c3 = decode(tape)
            p4, c4, _n4, kind4 = C.step(p, list(c), sd)
            if canon(p3, c3) != canon(p4, list(c4)) or kind != kind4:
                bad += 1
                print(f'  UNFAITHFUL step at p={p} chain={c!r} seed={sd}')
                break
            if kind == 'pred':          # the parameter-free branch
                V2 = full(p3, c3)
                want = D.pred(V)
                if V2 != want:
                    bad += 1
                    print(f'  PRED MISMATCH p={p} chain={c!r} seed={sd}')
                    break
            p, c, V = p3, c3, full(p3, c3)
            if not c:
                break
    print(f'  {trials} starts x up to {moves} moves: '
          + ('OK' if bad == 0 else f'{bad} FAILURES'))
    return bad == 0


def chain_level_fixed_run(p, c, seed, cap=200000):
    """The same fixed-parameter run at the chain level."""
    moves = 0
    c = list(c)
    while True:
        try:
            p, c, _, kind = C.step(p, c, seed)
        except C.Halt:
            return moves
        moves += 1
        if moves > cap:
            return None


def check_tape_vs_chain():
    print('tape layer == chain layer on the full fixed-parameter descent')
    ok = True
    for n in (1, 2, 3):
        for sn in (1, 2):
            p, c = chain_of(D.tower(n))
            mv_t, _ = super_run(encode(p, list(c)), sn)
            mv_c = chain_level_fixed_run(p, list(c), sn)
            same = (mv_t is None) == (mv_c is None) and \
                   (mv_t is None or mv_t == mv_c)
            ok = ok and same
            print(f'    eps_1[{n}], seed {sn}: tape {mv_t if mv_t is not None else ">cap"}'
                  f' vs chain {mv_c if mv_c is not None else ">cap"}'
                  + ('' if same else '   MISMATCH'))
    print('  ' + ('OK' if ok else 'FAILURES'))
    return ok


def record_lengths():
    print('measured record: fixed-parameter descent vs Hardy counts (no claim)')
    for n in (1, 2):
        V = D.tower(n)
        p, c = chain_of(V)
        for sn in (1, 2):
            fixed, _ = super_run(encode(p, list(c)), sn)
            hw, st = D.hardy(V, sn, cap=200000)
            print(f'    eps_1[{n}] seed {sn}: fixed-param descent '
                  f'{fixed if fixed is not None else ">200k"} moves; '
                  f'Hardy (bumping) {st if st is not None else ">200k"} steps')
    print('    (the f_{eps_1}(n) step-bound argument is ledger work, not here)')


def main():
    ok = check_codec()
    ok = check_moves() and ok
    ok = check_tape_vs_chain() and ok
    record_lengths()
    print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
