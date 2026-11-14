#!/usr/bin/env python3
"""Check the machine-14 right-buffer phase grammar and its local closure.

Grammar candidate:

    right = (V|C|C1|C2|P)* X* R

The script reports:
  * whether the grammar and the local no-bad predicate hold on the real block run;
  * the exact no-X right words observed;
  * local transitions from grammar-conforming states that leave the predicate.
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import product

import machine14_block_rules as blocks

PH = ("V", "C", "C1", "C2", "P")
LEFT = ("L", "U", "W", "F", "Y", "Q")
HEADS = ("<", ">", "w>")


def grammar(r: tuple[str, ...]) -> bool:
    i = 0
    while i < len(r) and r[i] in PH:
        i += 1
    while i < len(r) and r[i] == "X":
        i += 1
    return bool(r) and i == len(r) - 1 and r[-1] == "R"


def no_bad(head: str, l0: str | None, r: tuple[str, ...]) -> bool:
    if not r or not grammar(r):
        return False
    if head == ">" and r[0] == "R":
        return False
    if head == "w>" and len(r) > 1 and r[0] in ("C", "C1", "P") and r[1] == "R":
        return False
    if head == "<" and l0 == "L" and len(r) > 1 and r[0] in ("C", "C1", "P") and r[1] == "R":
        return False
    if head == "<" and l0 == "U" and r[0] == "R":
        return False
    if head == "<" and l0 == "Y" and r[0] in PH:
        return False
    return True


def right_words(maxlen: int):
    for p in range(maxlen + 1):
        for pref in product(PH, repeat=p):
            for x in range(maxlen - p + 1):
                yield pref + ("X",) * x + ("R",)


def scan(limit: int):
    tokens = ["L", "U", "Q", "R"]
    h, head = 3, "<"
    no_x: Counter[tuple[str, ...]] = Counter()
    grammar_bad = 0
    p_bad = 0
    first_g = None
    first_p = None
    for i in range(limit):
        left = tokens[:h]
        r = tuple(tokens[h:])
        l0 = left[-1] if left else None
        if "X" not in r[:-1]:
            no_x[r] += 1
        if not grammar(r):
            grammar_bad += 1
            first_g = first_g or (i, head, left, r)
        if not no_bad(head, l0, r):
            p_bad += 1
            first_p = first_p or (i, head, left, r)
        res = blocks.step(tokens, h, head)
        if res is None:
            return i, grammar_bad, p_bad, first_g, first_p, no_x
        tokens, h, head = res
    return limit, grammar_bad, p_bad, first_g, first_p, no_x


def closure(maxlen: int):
    violations = []
    checked = 0
    for head in HEADS:
        for l0 in LEFT:
            for r in right_words(maxlen):
                if not no_bad(head, l0, r):
                    continue
                checked += 1
                tokens = [l0] + list(r)
                res = blocks.step(tokens, 1, head)
                if res is None:
                    violations.append(("stuck", head, l0, r))
                    continue
                nt, nh, nhd = res
                nl = nt[:nh]
                nr = tuple(nt[nh:])
                nl0 = nl[-1] if nl else None
                if not no_bad(nhd, nl0, nr):
                    violations.append((head, l0, r, nhd, nl0, nr))
    return checked, violations


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("limit", nargs="?", type=int, default=1_000_000)
    ap.add_argument("--maxlen", type=int, default=7)
    args = ap.parse_args()
    steps, gbad, pbad, fg, fp, nox = scan(args.limit)
    print(f"steps={steps} grammar_violations={gbad} predicate_violations={pbad}")
    print(f"first_grammar={fg}")
    print(f"first_predicate={fp}")
    print("no-X right words:")
    for w, n in nox.most_common(10):
        print(f"  {w}: {n}")
    checked, viol = closure(args.maxlen)
    print(f"closure_checked={checked} closure_violations={len(viol)}")
    for v in viol[:10]:
        print(" ", v)


if __name__ == "__main__":
    main()
