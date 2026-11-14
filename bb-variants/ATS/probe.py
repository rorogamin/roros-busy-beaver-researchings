#!/usr/bin/env python3
"""Probe the long-run shape of an ATS orbit.

The default target is:

    1 1 1 0 fn(1) fn(1) fn(1) fn(0)

After a short warmup this orbit contains no primitive tokens.  The
reference list simulator is therefore replaced with a deque fast path; with
no primitive tokens the absorption phase is vacuous, so the fast path is
observationally identical to `ats.step_ats` on this state.

The probe reports the fixed core (the region from the first to the last
non-fn(1) token), the number of fn(1) tokens to its left and right, and the
total token/length/zero counts.  It is an empirical probe, not a proof of
non-halting.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from collections import deque
from typing import Sequence

import ats

DEFAULT_TARGET = "1 1 1 0 fn(1) fn(1) fn(1) fn(0)"


def core_bounds(tape: Sequence[ats.Token]) -> tuple[int, int] | None:
    indices = [i for i, tok in enumerate(tape) if tok != "1"]
    if not indices:
        return None
    return indices[0], indices[-1]


def core_of(tape: Sequence[ats.Token]) -> list[ats.Token]:
    bounds = core_bounds(tape)
    if bounds is None:
        return []
    return list(tape)[bounds[0] : bounds[1] + 1]


def fast_step(d: deque[ats.Token]) -> None:
    """One step when every token is a function (absorption is vacuous)."""
    head = d.popleft()

    if head == "1":
        d.extend(tuple(itertools.islice(d, 2)))
        return

    alpha = head
    c0 = alpha.count("0")
    c1 = alpha.count("1")

    if c1 == 0:
        return
    if c0 == 0:
        ats._one_rule(d, alpha)
        return
    if c1 > c0 or (c1 == c0 and alpha[0] == "1"):
        ats._one_rule(d, alpha)
        ats._zero_rule(d)
    else:
        ats._zero_rule(d)
        ats._one_rule(d, alpha)


def summarize(step: int, tape: Sequence[ats.Token]) -> None:
    bounds = core_bounds(tape)
    if bounds is None:
        print(f"{step:>9}  empty")
        return
    left = bounds[0]
    right = len(tape) - 1 - bounds[1]
    zeros = ats.count_zeros(tape)
    non_fn1 = sum(1 for tok in tape if tok != "1")
    print(
        f"{step:>9}  tokens={len(tape):>9}  length={ats.tape_length(tape):>9}  "
        f"zeros={zeros:>5}  non-fn1={non_fn1:>4}  "
        f"left={left:>9}  right={right:>9}"
    )


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tape", nargs="?", default=DEFAULT_TARGET)
    parser.add_argument("--warmup", type=int, default=1000)
    parser.add_argument("--steps", type=int, default=1_000_000)
    parser.add_argument("--interval", type=int, default=100_000)
    parser.add_argument("--show-core", action="store_true")
    args = parser.parse_args(argv)

    tape = ats.parse_tape(args.tape)
    for _ in range(args.warmup):
        if not tape:
            print(f"halted during warmup at step {_}")
            return
        ats.step_ats(tape)

    print("warmup:")
    summarize(args.warmup, tape)

    if not all(ats.is_fn(tok) for tok in tape):
        print("not all tokens are functions after warmup; use ats.py sim instead")
        sys.exit(2)

    reference_core = core_of(tape)
    d = deque(tape)
    steps = 0
    next_report = args.interval
    while d and steps < args.steps:
        fast_step(d)
        steps += 1
        if steps == next_report:
            summarize(args.warmup + steps, d)
            next_report += args.interval

    print("final:")
    summarize(args.warmup + steps, d)
    final_core = core_of(d)
    print(f"core unchanged: {final_core == reference_core} "
          f"({len(reference_core)} tokens)")
    if args.show_core:
        print("core:")
        print(ats.format_tape(reference_core))


if __name__ == "__main__":
    main()
