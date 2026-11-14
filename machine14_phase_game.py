#!/usr/bin/env python3
"""Forward phase-window search for machine 14's 19 block rules.

A window stores the head, up to KL nearest left tokens and up to KR nearest
right tokens, plus a `more` flag for each side.  Hidden tails are enumerated
nondeterministically when a rule consumes the last visible token.  Reaching a
window with head `>` and first right token `R` refutes a phase invariant of
that window size.  A completed BFS with no such window is a local candidate,
not yet a Lean proof.
"""
from __future__ import annotations

import argparse
from collections import deque
from itertools import product

LTOK = ("L", "U", "W", "F", "Y", "Q")
RTOK = ("R", "X", "V", "C", "C1", "C2", "P")
HEADS = ("<", ">", "w>")


def side_windows(alpha: tuple[str, ...], k: int):
    out = []
    for n in range(k):
        for w in product(alpha, repeat=n):
            out.append((w, False))
    for w in product(alpha, repeat=k):
        out.append((w, False))
        out.append((w, True))
    return out


def norm(seq, more, alpha, k):
    seq = tuple(seq)
    if len(seq) > k:
        return seq[:k], True
    if len(seq) < k:
        return seq, False
    return seq, more


def pop_side(seq, more, alpha, k):
    if not seq:
        return []
    hd, rest = seq[0], seq[1:]
    if len(rest) < k and more:
        return [(hd, tuple(rest + (x,)), True) for x in alpha]
    return [(hd, rest, more)]


def step_window(a, kl, kr):
    h, L, Lm, R, Rm = a
    out = set()

    def emit(nh, nL, nLm, nR, nRm):
        nL, nLm = norm(nL, nLm, LTOK, kl)
        nR, nRm = norm(nR, nRm, RTOK, kr)
        out.add((nh, nL, nLm, nR, nRm))

    if h == "<":
        for x, nL, nm in pop_side(L, Lm, LTOK, kl):
            if x == "W":
                emit("<", nL, nm, ("V",) + R, Rm)
            elif x == "U":
                emit(">", ("W",) + nL, nm, R, Rm)
            elif x == "L":
                emit("w>", ("L",) + nL, nm, R, Rm)
            elif x == "Y":
                emit("<", nL, nm, ("X",) + R, Rm)
            elif x == "F":
                emit("<", nL, nm, ("C",) + R, Rm)
            elif x == "Q":
                emit("<", nL, nm, ("P",) + R, Rm)
        return out

    for x, nR, nm in pop_side(R, Rm, RTOK, kr):
        if h == ">":
            if x == "V":
                emit(">", ("U",) + L, Lm, nR, nm)
            elif x == "X":
                emit("<", L, Lm, ("C1", "P") + nR, nm)
            elif x == "C":
                emit("<", L, Lm, ("C1",) + nR, nm)
            elif x == "C1":
                emit("<", L, Lm, ("C2",) + nR, nm)
            elif x == "C2":
                emit(">", ("F",) + L, Lm, nR, nm)
            elif x == "P":
                emit("w>", L, Lm, nR, nm)
        else:
            if x == "V":
                emit("w>", ("U",) + L, Lm, nR, nm)
            elif x == "X":
                emit("w>", ("Y",) + L, Lm, nR, nm)
            elif x == "R":
                emit("<", L, Lm, ("X", "R") + nR, nm)
            elif x == "C":
                emit(">", ("Q", "F") + L, Lm, nR, nm)
            elif x == "C1":
                emit(">", ("Q", "U") + L, Lm, nR, nm)
            elif x == "C2":
                emit("w>", ("W",) + L, Lm, nR, nm)
            elif x == "P":
                emit(">", ("U",) + L, Lm, nR, nm)
    return out


def fmt(a):
    h, L, Lm, R, Rm = a
    left = "".join(L) + ("..." if Lm else "")
    right = "".join(R) + ("..." if Rm else "")
    return f"{h} | L={left or '-'} | R={right or '-'}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("kl", type=int)
    ap.add_argument("kr", type=int)
    ap.add_argument("--limit", type=int, default=2_000_000)
    args = ap.parse_args()

    init = ("<", ("Q", "U"), True, ("R",), False)
    seen = {init}
    q = deque([init])
    prev = {init: None}
    bad = None

    while q and len(seen) < args.limit:
        a = q.popleft()
        h, L, Lm, R, Rm = a
        if h == ">" and R and R[0] == "R":
            bad = a
            break
        for b in step_window(a, args.kl, args.kr):
            if b not in seen:
                seen.add(b)
                prev[b] = a
                q.append(b)

    print(f"windows={len(seen)} queue={len(q)} bad={fmt(bad) if bad else None}")
    if bad:
        path = []
        x = bad
        while x is not None:
            path.append(x)
            x = prev[x]
        path.reverse()
        print(f"path_length={len(path) - 1}")
        for i, a in enumerate(path[:30]):
            print(f"{i:2d} {fmt(a)}")


if __name__ == "__main__":
    main()
