#!/usr/bin/env python3
"""Single-head block simulator for BB(2,5) machine 14.

Machine: 1RB2LA0RB4LB1RA_1LA3RA1RA---0LA

The block alphabet and rules are hipparcos's 2025-11-06 analysis:

  L  = ^11
  R  = 1$       (represented by the block R; $ is the blank tail)
  X  = 142
  Y  = 031
  U  = 01
  W  = 11
  V  = 22
  C  = 14
  F  = 03
  C1 = 24
  C2 = 21
  P  = 2
  Q  = 1

The head is at a boundary.  '<' reads the block on its left; '>' and 'w>'
read the block on their right.  The simulation starts after 14 base steps at

  L U Q < R

This is a macro model, not a proof by itself.  A run that never encounters a
block outside the rule domain is evidence that the rules are total on that
trajectory; it is not evidence that every reachable configuration is covered.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter


def step(tokens: list[str], h: int, head: str):
    """Return (new_tokens, new_boundary, new_head), or None if no rule applies."""
    if head == "<":
        if h <= 0:
            return None
        x = tokens[h - 1]
        if x == "W":                       # W < -> < V
            return tokens[:h - 1] + ["V"] + tokens[h:], h - 1, "<"
        if x == "U":                       # U < -> W >
            return tokens[:h - 1] + ["W"] + tokens[h:], h, ">"
        if x == "L":                       # L < -> L w>
            return tokens, h, "w>"
        if x == "Y":                       # Y < -> < X
            return tokens[:h - 1] + ["X"] + tokens[h:], h - 1, "<"
        if x == "F":                       # F < -> < C
            return tokens[:h - 1] + ["C"] + tokens[h:], h - 1, "<"
        if x == "Q":                       # Q < -> < P
            return tokens[:h - 1] + ["P"] + tokens[h:], h - 1, "<"
        return None

    if head == ">":
        if h >= len(tokens):
            return None
        x = tokens[h]
        if x == "V":                       # > V -> U >
            return tokens[:h] + ["U"] + tokens[h + 1:], h + 1, ">"
        if x == "X":                       # > X -> < C1 P
            return tokens[:h] + ["C1", "P"] + tokens[h + 1:], h, "<"
        if x == "C":                       # > C -> < C1
            return tokens[:h] + ["C1"] + tokens[h + 1:], h, "<"
        if x == "C1":                      # > C1 -> < C2
            return tokens[:h] + ["C2"] + tokens[h + 1:], h, "<"
        if x == "C2":                      # > C2 -> F >
            return tokens[:h] + ["F"] + tokens[h + 1:], h + 1, ">"
        if x == "P":                       # > P -> w>
            return tokens[:h] + tokens[h + 1:], h, "w>"
        return None

    if head == "w>":
        if h >= len(tokens):
            return None
        x = tokens[h]
        if x == "V":                       # w> V -> U w>
            return tokens[:h] + ["U"] + tokens[h + 1:], h + 1, "w>"
        if x == "X":                       # w> X -> Y w>
            return tokens[:h] + ["Y"] + tokens[h + 1:], h + 1, "w>"
        if x == "R":                       # w> R -> < X R
            return tokens[:h] + ["X", "R"] + tokens[h + 1:], h, "<"
        if x == "C":                       # w> C -> F Q >
            return tokens[:h] + ["F", "Q"] + tokens[h + 1:], h + 2, ">"
        if x == "C1":                      # w> C1 -> U Q >
            return tokens[:h] + ["U", "Q"] + tokens[h + 1:], h + 2, ">"
        if x == "C2":                      # w> C2 -> W w>
            return tokens[:h] + ["W"] + tokens[h + 1:], h + 1, "w>"
        if x == "P":                       # w> P -> U >
            return tokens[:h] + ["U"] + tokens[h + 1:], h + 1, ">"
        return None

    return None


def show(tokens: list[str], h: int, head: str) -> str:
    return " ".join(tokens[:h] + [head] + tokens[h:])


def run(limit: int) -> dict:
    tokens = ["L", "U", "Q", "R"]
    h = 3
    head = "<"
    contexts: Counter[tuple[str, str]] = Counter()
    max_blocks = len(tokens)

    for i in range(limit):
        if head == "<":
            read = tokens[h - 1] if h > 0 and h - 1 < len(tokens) else None
        else:
            read = tokens[h] if 0 <= h < len(tokens) else None
        contexts[(head, str(read))] += 1

        result = step(tokens, h, head)
        if result is None:
            return {
                "limit": limit,
                "steps": i,
                "stuck": True,
                "head": head,
                "left": tokens[:h],
                "right": tokens[h:],
            }

        tokens, h, head = result
        max_blocks = max(max_blocks, len(tokens))

    return {
        "limit": limit,
        "steps": limit,
        "stuck": False,
        "head": head,
        "blocks": len(tokens),
        "max_blocks": max_blocks,
        "left_tail": tokens[max(0, h - 10):h],
        "right_tail": tokens[h:h + 10],
        "contexts": {f"{head} {read}": count for (head, read), count in contexts.items()},
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("limit", nargs="?", type=int, default=1_000_000)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    result = run(args.limit)
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"limit={result['limit']} steps={result['steps']} stuck={result['stuck']}")
        if result["stuck"]:
            print(f"stuck head={result['head']} left={result['left']} right={result['right']}")
        else:
            print(f"blocks={result['blocks']} max_blocks={result['max_blocks']}")
            print("left_tail=" + " ".join(result["left_tail"]))
            print("right_tail=" + " ".join(result["right_tail"]))


if __name__ == "__main__":
    main()
