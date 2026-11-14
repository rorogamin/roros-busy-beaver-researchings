#!/usr/bin/env python3
"""Search simple relations between machine 14's clean left counter and right X-buffer.

The left stack is stored far-to-near in this simulator.  `cval` ignores the
transient Q/Y tokens and reads U/W/F over the far-end L exactly as the related
13-machine family does.  The right buffer is the number of X tokens.

This is a search script, not a proof: it reports which relations survive a
finite prefix of the block run and which fail with a concrete witness.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict

import machine14_block_rules as blocks


def cval(left: list[str]) -> int:
    v = 0
    for x in left:
        if x in ("L", "Q", "Y"):
            continue
        if x == "U":
            v = 2 * v + 1
        elif x == "W":
            v = 2 * v
        elif x == "F":
            v //= 2
    return v


def run(limit: int) -> dict:
    tokens = ["L", "U", "Q", "R"]
    h, head = 3, "<"
    candidates = {
        "cval >= xcount": lambda c, x: c >= x,
        "cval <= xcount": lambda c, x: c <= x,
        "cval == xcount": lambda c, x: c == x,
        "cval >= 2*xcount": lambda c, x: c >= 2 * x,
        "cval <= 2*xcount": lambda c, x: c <= 2 * x,
        "cval == 0 iff xcount == 0": lambda c, x: (c == 0) == (x == 0),
        "cval == 0 implies xcount == 0": lambda c, x: c != 0 or x == 0,
        "xcount <= 6": lambda c, x: x <= 6,
        "cval + xcount even": lambda c, x: (c + x) % 2 == 0,
        "cval - xcount even": lambda c, x: (c - x) % 2 == 0,
    }
    failures = {name: 0 for name in candidates}
    first = {}
    samples = defaultdict(lambda: [10**18, -1, 0])
    congruences = {
        (a, b, c, m): True
        for m in range(2, 9)
        for a in range(m)
        for b in range(m)
        for c in range(m)
    }

    for step in range(limit):
        left = tokens[:h]
        right = tokens[h:]
        cv = cval(left)
        xc = right.count("X")
        key = (head, min(cv, 16), min(xc, 8))
        samples[key][0] = min(samples[key][0], cv)
        samples[key][1] = max(samples[key][1], cv)
        samples[key][2] += 1

        for name, pred in candidates.items():
            if not pred(cv, xc):
                failures[name] += 1
                first.setdefault(name, (step, head, left, right, cv, xc))

        for (a, b, c, m) in list(congruences):
            if (a * cv + b * xc - c) % m != 0:
                del congruences[(a, b, c, m)]

        result = blocks.step(tokens, h, head)
        if result is None:
            return {
                "limit": limit,
                "stuck_at": step,
                "failures": failures,
                "first": first,
                "surviving_congruences": list(congruences),
                "samples": samples,
            }
        tokens, h, head = result

    return {
        "limit": limit,
        "stuck_at": None,
        "failures": failures,
        "first": first,
        "surviving_congruences": list(congruences),
        "samples": samples,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("limit", nargs="?", type=int, default=1_000_000)
    args = ap.parse_args()
    out = run(args.limit)
    print(f"limit={out['limit']} stuck_at={out['stuck_at']}")
    print("candidate failures:")
    for name, count in out["failures"].items():
        print(f"  {name:32s} violations={count}")
        if count and name in out["first"]:
            print(f"    first={out['first'][name]}")
    print("surviving congruences a*cval+b*xcount=c mod m:")
    print(out["surviving_congruences"])
    print("observed cval range by (head, xcount bucket):")
    by = defaultdict(lambda: [10**18, -1])
    for (head, _cv, xc), (lo, hi, _n) in out["samples"].items():
        a = by[(head, xc)]
        a[0] = min(a[0], lo)
        a[1] = max(a[1], hi)
    for key in sorted(by, key=str):
        print(f"  {key}: cval {by[key][0]}..{by[key][1]}")


if __name__ == "__main__":
    main()
