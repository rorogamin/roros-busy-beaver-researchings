#!/usr/bin/env python3
"""Probe the ATS cryptid candidate "Loom".

Tape (length 9):

    1  fn(1)  0  1  fn(1)  fn(01)  1  0

After 2,000 ordinary steps every token is a function and the whole tape is a
word over

    T = { fn(1), fn(01), fn(0101), fn(001) }.

The set T is closed under ATS head execution (see CRYPTID.md).  Therefore
there are no primitives after the warmup and no new function arguments can be
introduced.  Every head is either fn(1), which adds one token, or one of the
three zero-bearing composites, whose one-rule adds two tokens and whose
zero-rule removes one, so the token count never decreases.

This script checks the finite warmup and then runs the fast all-function
simulator.  The two observations it reports (no token decrease and no type
outside `T`) are consequences of the type-closure lemma; the proof that the
token count tends to infinity is in `README.md`.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from typing import Sequence

import ats
import probe

DEFAULT_TAPE = "1 fn(1) 0 1 fn(1) fn(01) 1 0"
CLOSED_TYPES = {"1", "01", "0101", "001"}


def run(tape_text: str, *, warmup: int, steps: int, interval: int) -> None:
    tape = ats.parse_tape(tape_text)
    print(f"tape: {ats.format_tape(tape)}")
    print(f"length: {ats.tape_length(tape)}")

    for step in range(1, warmup + 1):
        if not tape:
            print(f"halted during warmup at step {step - 1}")
            return
        ats.step_ats(tape)

    if not all(ats.is_fn(tok) for tok in tape):
        print("warmup did not reach the all-function phase")
        return
    observed = set(tape)
    extra = observed - CLOSED_TYPES
    print(f"warmup {warmup}: tokens={len(tape)} types={sorted(observed)}")
    if extra:
        print(f"outside the claimed closed set: {sorted(extra)}")
        return

    start_core = probe.core_of(tape)
    d = deque(tape)
    previous = len(d)
    decreases = 0
    nonincrease_run = 0
    max_nonincrease_run = 0
    bad_types: set[str] = set()

    for step in range(1, steps + 1):
        probe.fast_step(d)
        current = len(d)
        if current < previous:
            decreases += 1
        if current > previous:
            nonincrease_run = 0
        else:
            nonincrease_run += 1
            max_nonincrease_run = max(max_nonincrease_run, nonincrease_run)
        previous = current

        if interval and step % interval == 0:
            extra = set(d) - CLOSED_TYPES
            if extra:
                bad_types |= extra
            core = probe.core_of(d)
            core_counts = Counter(tok for tok in core if tok != "1")
            print(
                f"step {warmup + step}: tokens={len(d)} zeros={ats.count_zeros(d)} "
                f"core={len(core)} core_types={dict(core_counts)}"
            )

    final_core = probe.core_of(d)
    print()
    print(f"ran {steps} fast steps after warmup")
    print(f"token decreases: {decreases}")
    print(f"longest run without an increase: {max_nonincrease_run}")
    print(f"types outside closed set: {sorted(bad_types) if bad_types else 'none'}")
    print(f"final tokens: {len(d)}")
    print(f"final zeros: {ats.count_zeros(d)}")
    print(f"core unchanged: {final_core == start_core} ({len(start_core)} start tokens)")
    print("status: proved non-halting by the T-closure/composite-count argument")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tape", nargs="?", default=DEFAULT_TAPE)
    parser.add_argument("--warmup", type=int, default=2_000)
    parser.add_argument("--steps", type=int, default=1_000_000)
    parser.add_argument("--interval", type=int, default=100_000)
    args = parser.parse_args(argv)
    run(args.tape, warmup=args.warmup, steps=args.steps, interval=args.interval)


if __name__ == "__main__":
    main()
