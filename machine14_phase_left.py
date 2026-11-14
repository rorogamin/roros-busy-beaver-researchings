#!/usr/bin/env python3
"""Test the phase predicate with a left-context gate.

The Python block model stores the left buffer far-to-near, so a valid left
word has the form

    L (U|W|F|Y|Q)*

(`L` is the far end and `left[-1]` is the nearest token).  The gate is:

  * the left word is valid (`L` first, no other `L`),
  * a `>` head has at least two left blocks, and
  * the local sources `< L F R`, `< L Q R`, `< ... Y W ...`,
    `< ... Y F ...`, and `< ... Y Q ...` are excluded,
  * and the `> V R` source is excluded.

The length condition excludes the four bare-left source patterns
`> V R`, `> C R`, `> C2 R`, and `> P C R`, all of which have left `L`.
The two `<` F/Q exclusions are the first new failures found after adding that
gate.  The `Y W`, `Y F`, and `Y Q` exclusions apply with any right buffer,
because the target is already forbidden as soon as the source reads `W`, `F`,
or `Q` after `Y`.  The `> V R` rule is a source exclusion: it steps to the
`> U R` dead end.

The script scans the real run and then performs a bounded closure search over
valid left words and grammar-conforming right words.  A finite closure search
is a search result, not a proof of closure.
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import product

import machine14_block_rules as blocks
from machine14_phase_grammar import PH, grammar, no_bad

INNER = ("U", "W", "F", "Y", "Q")
HEADS = ("<", ">", "w>")
LMOVE = ("W", "F", "Q", "Y")


def left_ok(left: tuple[str, ...]) -> bool:
    return bool(left) and left[0] == "L" and "L" not in left[1:]


def left_gate(head: str, left: tuple[str, ...]) -> bool:
    return left_ok(left) and (head != ">" or len(left) >= 2)


def bad_left_phase(head: str, left: tuple[str, ...],
                   right: tuple[str, ...]) -> bool:
    """The checked local left-phase source exclusions.

    The left buffer is stored far-to-near, so the first two patterns are
    exactly `L F` and `L Q` immediately before the head.  The rest is the
    backward-closed `< Y` family: scan the nearest run of `W/F/Q/Y` and reject
    it if it contains a far-to-near `Y W`, `Y F`, or `Y Q` pair.
    """
    if head != "<" or len(left) < 2:
        return False
    if left[-2:] in (("L", "F"), ("L", "Q")) and right == ("R",):
        return True
    i = len(left)
    while i > 0 and left[i - 1] in LMOVE:
        i -= 1
    return any(left[j] == "Y" and left[j + 1] in ("W", "F", "Q")
               for j in range(i, len(left) - 1))


def bad_right_source(head: str, right: tuple[str, ...]) -> bool:
    """The checked `> V R` dead-end source exclusion."""
    return head == ">" and right == ("V", "R")


def bad_source(head: str, left: tuple[str, ...],
               right: tuple[str, ...]) -> bool:
    return (bad_left_phase(head, left, right) or
            bad_right_source(head, right))


def phase_ok(head: str, left: tuple[str, ...], right: tuple[str, ...]) -> bool:
    return (grammar(right) and
            no_bad(head, left[-1] if left else None, right) and
            left_gate(head, left) and
            not bad_source(head, left, right))


def left_words(maxlen: int):
    yield ("L",)
    for n in range(2, maxlen + 1):
        for p in product(INNER, repeat=n - 1):
            yield ("L",) + p


def right_words(maxlen: int):
    for p in range(maxlen + 1):
        for pref in product(PH, repeat=p):
            for x in range(maxlen - p + 1):
                yield pref + ("X",) * x + ("R",)


def scan(limit: int):
    tokens = ["L", "U", "Q", "R"]
    h, head = 3, "<"
    bad = 0
    first = None
    for i in range(limit):
        left = tuple(tokens[:h])
        right = tuple(tokens[h:])
        if not phase_ok(head, left, right):
            bad += 1
            first = first or (i, head, left, right)
        res = blocks.step(tokens, h, head)
        if res is None:
            return i, bad, first
        tokens, h, head = res
    return limit, bad, first


def closure(maxleft: int, maxright: int):
    checked = 0
    violations = []
    for head in HEADS:
        for left in left_words(maxleft):
            if not left_gate(head, left):
                continue
            for right in right_words(maxright):
                if not phase_ok(head, left, right):
                    continue
                checked += 1
                tokens = list(left) + list(right)
                res = blocks.step(tokens, len(left), head)
                if res is None:
                    violations.append(("stuck", head, left, right))
                    continue
                nt, nh, nhd = res
                nl = tuple(nt[:nh])
                nr = tuple(nt[nh:])
                if not phase_ok(nhd, nl, nr):
                    violations.append((head, left, right, nhd, nl, nr))
    return checked, violations


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("limit", nargs="?", type=int, default=1_000_000)
    ap.add_argument("--maxleft", type=int, default=5)
    ap.add_argument("--maxright", type=int, default=4)
    args = ap.parse_args()

    steps, bad, first = scan(args.limit)
    print(f"actual_steps={steps} combined_violations={bad} first={first}")

    # The four old sources all have left='L' and are rejected by the gate.
    old = [
        (">", ("L",), ("V", "R")),
        (">", ("L",), ("C", "R")),
        (">", ("L",), ("C2", "R")),
        (">", ("L",), ("P", "C", "R")),
    ]
    print("old_sources_blocked=" +
          str(all(not left_gate(h, l) for h, l, _ in old)))

    new = [
        ("<", ("L", "F"), ("R",)),
        ("<", ("L", "Q"), ("R",)),
        ("<", ("L", "Y", "W"), ("R",)),
        ("<", ("L", "Y", "W"), ("X", "R")),
        ("<", ("L", "Y", "F"), ("R",)),
        ("<", ("L", "Y", "F"), ("X", "R")),
        ("<", ("L", "Y", "Q"), ("R",)),
        ("<", ("L", "Y", "Q"), ("X", "R")),
        ("<", ("L", "Y", "W", "W"), ("R",)),
        (">", ("L", "U"), ("V", "R")),
    ]
    print("new_sources_blocked=" +
          str(all(bad_source(h, l, r) for h, l, r in new)))

    checked, violations = closure(args.maxleft, args.maxright)
    print(f"closure_left<={args.maxleft} right<={args.maxright} "
          f"checked={checked} violations={len(violations)}")
    for v in violations[:10]:
        print(" ", v)


if __name__ == "__main__":
    main()
