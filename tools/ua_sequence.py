#!/usr/bin/env python3
"""Reference generator for the greedy U-a-U-free sequence.

Alphabet: 0,1,2,...  A finite word is legal iff it contains no factor
U a U with a a single symbol and U a nonempty word.  At each step choose the
smallest symbol that keeps the word legal.

Let R be the reverse of the current word and Z its Z-array.  A candidate c is
forbidden exactly when

    exists L >= 1:  R[L] == c  and  Z[L+1] >= L-1.

This is the reversed form of the factor condition: the first U is
R[L+1:L+1+L-1] reversed, the middle is R[L], and the second U is the prefix
R[0:L-1] reversed.

The C++ version (ua_sequence.cpp) is the fast one for 200,000+ terms.  This
Python version is a readable reference and a brute-force cross-check.
"""
from __future__ import annotations

import argparse
from collections import Counter


def extend_z(word_rev: list[int], z: list[int], c: int) -> tuple[list[int], list[int]]:
    """Prepend c to word_rev and update its Z-array."""
    n = len(word_rev)
    new_z = [0] * (n + 1)
    new_z[0] = n + 1
    for i in range(1, n + 1):
        if word_rev[i - 1] == c:
            new_z[i] = 1 + (z[i] if i < n else 0)
    return [c, *word_rev], new_z


def forbidden_symbols(word_rev: list[int], z: list[int]) -> set[int]:
    n = len(word_rev)
    out: set[int] = set()
    for L in range(1, n // 2 + 1):
        cond = (L == 1) if L + 1 >= n else (z[L + 1] >= L - 1)
        if cond and L < n:
            out.add(word_rev[L])
    return out


def generate(limit: int = 200_000, stop_at_five: bool = True):
    word: list[int] = []
    word_rev: list[int] = []
    z: list[int] = []
    first: dict[int, int] = {}
    counts: Counter[int] = Counter()
    halt_at: int | None = None
    for pos in range(1, limit + 1):
        forb = forbidden_symbols(word_rev, z)
        c = 0
        while c in forb:
            c += 1
        first.setdefault(c, pos)
        counts[c] += 1
        if stop_at_five and c >= 5:
            halt_at = pos
            break
        word.append(c)
        word_rev, z = extend_z(word_rev, z, c)
    return word, first, counts, halt_at


def brute_ok(seq: list[int], c: int) -> bool:
    """Whether appending c creates U-a-U (contiguous), via direct search."""
    t = seq + [c]
    n = len(t)
    for L in range(1, (n - 1) // 2 + 1):
        for i in range(0, n - 2 * L):
            if t[i : i + L] == t[i + L + 1 : i + 2 * L + 1]:
                return False
    # Also catch a factor ending at the new last symbol.
    for L in range(1, (n - 1) // 2 + 1):
        if t[n - 2 * L - 1 : n - L - 1] == t[n - L :]:
            return False
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=20000)
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--check", type=int, default=0, help="brute-check this many terms")
    ap.add_argument("--no-stop", action="store_true")
    args = ap.parse_args()

    word, first, counts, halt_at = generate(args.limit, not args.no_stop)
    mx = max(first) if first else -1
    print(f"terms={len(word)} halt_at={halt_at} max={mx}")
    for v in range(mx + 1):
        print(f"value={v} first={first.get(v)} count={counts.get(v,0)}")
    if args.dump:
        print("SEQ", "".join(str(x) for x in word))
    if args.check:
        test, _, _, _ = generate(args.check, stop_at_five=True)
        seq: list[int] = []
        for pos, c in enumerate(test):
            if not brute_ok(seq, c):
                print(f"BRUTE MISMATCH at position {pos+1}: c={c}")
                return 1
            seq.append(c)
        print(f"brute-check OK for first {len(test)} terms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
