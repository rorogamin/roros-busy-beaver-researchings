#!/usr/bin/env python3
"""Probe the ATS cryptid candidate "Rattle".

Initial tape (ATS length 14):

    fn(11111)  fn(1)  fn(0011)  fn(1)  fn(01)  fn(0)

This tape starts in the all-function phase, so absorption is vacuous and the
simulation can use the fast path.  The candidate was selected because:

  * it has no zero-free classification;
  * no exact cycle has been observed;
  * its type set is larger than the fixed-core length-8/Loom examples;
  * its core is not fixed: the `fn(11)` and `fn(01)` counts keep moving.

It is a candidate, not a proved non-halting machine.  The open question is
whether the core counts eventually lock or whether the orbit has a genuinely
new invariant.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from typing import Sequence

import ats
import probe

TAPE = ["11111", "1", "0011", "1", "01", "0"]


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
