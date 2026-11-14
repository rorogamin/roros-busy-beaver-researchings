#!/usr/bin/env python3
"""Probe the ATS cryptid candidate "Grove".

Initial tape (ATS length 32):

    fn(010) fn(011) fn(00011000) fn(111) fn(1111111)
    fn(10) fn(10) fn(0001)

This starts in the all-function phase, so absorption is vacuous and the fast
simulator applies.  It was selected from an all-function random search because
its core does not settle: the `fn(11)` and `fn(111)` counts grow for millions
of steps, while the zero count stays fixed.

It is a candidate, not a proved non-halting machine.  It is not classified by
the zero-free, cycle, or fixed-core deciders used in this directory.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from typing import Sequence

import ats
import probe

TAPE = ["010", "011", "00011000", "111", "1111111", "10", "10", "0001"]


def run(*, steps: int, interval: int) -> None:
    d = deque(TAPE)
    print(f"tape: {ats.format_tape(TAPE)}")
    print(f"length: {ats.tape_length(TAPE)}")
    print(f"start zeros: {ats.count_zeros(TAPE)}")

    previous = len(d)
    decreases = 0
    max_without_increase = 0
    without_increase = 0
    types: set[str] = set(d)

    for step in range(1, steps + 1):
        probe.fast_step(d)
        current = len(d)
        if current < previous:
            decreases += 1
        if current > previous:
            without_increase = 0
        else:
            without_increase += 1
            max_without_increase = max(max_without_increase, without_increase)
        previous = current

        if interval and step % interval == 0:
            types.update(d)
            core = probe.core_of(d)
            core_counts = Counter(tok for tok in core if tok != "1")
            print(
                f"step {step}: tokens={len(d)} zeros={ats.count_zeros(d)} "
                f"core={len(core)} core_types={dict(core_counts)}"
            )

    final_core = probe.core_of(d)
    print()
    print(f"ran {steps} steps")
    print(f"token decreases: {decreases}")
    print(f"longest run without an increase: {max_without_increase}")
    print(f"observed types: {sorted(types)}")
    print(f"final tokens: {len(d)}")
    print(f"final zeros: {ats.count_zeros(d)}")
    print(f"final core: {len(final_core)} tokens; types "
          f"{dict(Counter(tok for tok in final_core if tok != '1'))}")
    print("status: cryptid candidate; no halting proof")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=1_000_000)
    parser.add_argument("--interval", type=int, default=200_000)
    args = parser.parse_args(argv)
    run(steps=args.steps, interval=args.interval)


if __name__ == "__main__":
    main()
