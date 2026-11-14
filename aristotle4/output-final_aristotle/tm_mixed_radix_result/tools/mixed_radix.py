#!/usr/bin/env python3
"""Exact mixed-radix accelerator for 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA.

A successful macro enters a word in A and returns one cell to its left in B.
It uses the conditional, context-independent identities
    F(42 x) = 44 x,       cost 3
    F(44 x) = 42 F(x),    cost 4 + cost(F,x)
    F(2 x) = 2 F^3(x),    cost 4 + cost(F^3,x).
A failed macro plan changes nothing and the simulator performs one literal
transition. All counters use Python arbitrary-precision integers.

This program is NOT a Lean-checked proof or a nonhalting decision procedure.
See ../RESULTS.md for the mathematical argument and verification limits.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import random
import time
from typing import Optional

# Transition = (new symbol, head displacement, new state); A=0, B=1.
Transition = tuple[int, int, int]
TABLE: tuple[tuple[Optional[Transition], ...], ...] = (
    ((1, 1, 1), None, (3, 1, 0), (2, -1, 0), (2, 1, 1)),
    ((2, -1, 1), (3, -1, 0), (4, -1, 1), (4, 1, 0), (0, 1, 0)),
)


@dataclass(frozen=True)
class Plan:
    edits: tuple[tuple[int, int], ...]
    cost: int
    end: int  # First cell following the finite token prefix used.


def plan_return(tape: list[int], pos: int, repetitions: int = 1) -> Optional[Plan]:
    """Plan virtual F^repetitions; return None if its carry cannot be resolved.

    No tape mutation occurs during planning. For repetitions > 1, the time
    cost excludes the virtual restarts of F at the left edge. Only a plan
    with repetitions == 1 is directly used as a TM macro.
    """
    if repetitions < 0:
        raise ValueError("repetitions must be nonnegative")
    if not 0 <= pos < len(tape):
        raise IndexError("macro position outside allocated tape")
    i, k, cost = pos, repetitions, 0
    edits: list[tuple[int, int]] = []
    while k:
        if i >= len(tape):
            raise RuntimeError("macro reached allocated tape boundary")
        if tape[i] == 2:
            cost += 4 * k
            k *= 3
            i += 1
        elif tape[i] == 4 and i + 1 < len(tape) and tape[i + 1] in (2, 4):
            bit = int(tape[i + 1] == 4)
            carry, next_bit = divmod(k + bit, 2)
            edits.append((i + 1, 2 + 2 * next_bit))
            cost += 3 * k + carry
            k = carry
            i += 2
        else:
            return None
    return Plan(tuple(edits), cost, i)


class Machine:
    def __init__(self, cells: int = 200_000) -> None:
        if cells < 100:
            raise ValueError("allocate at least 100 cells")
        self.tape = [0] * cells
        self.origin = cells // 2
        self.p = self.origin
        self.q = 0
        self.t = 0
        self.lo = self.hi = self.p
        self.macros = self.micro = 0

    def advance(self, target: int, *, slow: bool = False) -> bool:
        """Take one literal step or a proven macro without overshooting target.

        False means the machine is scanning A/1 (the undefined transition).
        """
        if self.t >= target:
            raise ValueError("advance requires a future target")
        transition = TABLE[self.q][self.tape[self.p]]
        if transition is None:
            return False
        plan = plan_return(self.tape, self.p) if self.q == 0 and not slow else None
        if plan is not None and plan.cost <= target - self.t:
            for i, symbol in plan.edits:
                self.tape[i] = symbol
            self.p -= 1
            self.q = 1
            self.t += plan.cost
            self.macros += 1
        else:
            symbol, direction, self.q = transition
            self.tape[self.p] = symbol
            self.p += direction
            self.t += 1
            self.micro += 1
        self.lo = min(self.lo, self.p)
        self.hi = max(self.hi, self.p)
        if self.lo < 2 or self.hi >= len(self.tape) - 2:
            raise RuntimeError("allocated tape storage exhausted")
        return True

    def snapshot(self) -> dict:
        return {
            "t": str(self.t), "p": self.p - self.origin, "q": self.q,
            "lo": self.lo - self.origin, "hi": self.hi - self.origin,
            "macros": self.macros, "micro": self.micro,
            "tape": "".join(map(str, self.tape[self.lo:self.hi + 1])),
        }


def selftest() -> dict:
    """Test each macro against literal transitions and a complete initial run."""
    rng = random.Random(175901)
    single_checks = batch_checks = 0
    for batched, samples in ((False, 2000), (True, 1000)):
        for _ in range(samples):
            tape = [0, 1] + [rng.choice([2, 4]) for _ in range(rng.randrange(1, 20))]
            tape += [3, 2, 0, 0]
            k = rng.randrange(1, 25) if batched else 1
            plan = plan_return(tape, 2, k)
            if plan is None or plan.cost > 200_000:
                continue
            expected = tape.copy()
            for i, value in plan.edits:
                expected[i] = value
            total = 0
            for _ in range(k):
                p, q = 2, 0  # Virtual restart, deliberately costs zero.
                while p >= 2:
                    tr = TABLE[q][tape[p]]
                    assert tr is not None, "macro concealed a halt"
                    value, direction, q = tr
                    tape[p] = value
                    p += direction
                    total += 1
                    assert total <= plan.cost, "macro time undercount"
                assert (p, q) == (1, 1)
            assert (total, tape) == (plan.cost, expected)
            if batched:
                batch_checks += 1
            else:
                single_checks += 1

    target = 1_000_000
    fast = Machine(cells=500)
    slow = Machine(cells=500)
    endpoints = 0
    while fast.t < target:
        assert fast.advance(target)
        while slow.t < fast.t:
            assert slow.advance(fast.t, slow=True)
        assert (slow.q, slow.p, slow.tape) == (fast.q, fast.p, fast.tape)
        endpoints += 1
    return {
        "random_single_return_checks": single_checks,
        "random_batch_checks": batch_checks,
        "literal_differential_steps": target,
        "literal_differential_endpoints": endpoints,
        "status": "PASS",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--power", type=int, default=100, help="run to exactly 10**power transitions")
    parser.add_argument("--target", type=int, help="alternative exact nonnegative transition target")
    parser.add_argument("--test", action="store_true", help="run differential tests first")
    parser.add_argument("--test-only", action="store_true", help="run tests without the long run")
    parser.add_argument("--slow", action="store_true", help="use literal transitions only")
    parser.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    if args.power < 0 or (args.target is not None and args.target < 0):
        parser.error("target and power must be nonnegative")
    if args.test or args.test_only:
        print(json.dumps(selftest()), flush=True)
    if args.test_only:
        return
    target = args.target if args.target is not None else 10 ** args.power
    machine = Machine()
    start = time.monotonic()
    status = "REACHED_TARGET"
    while machine.t < target:
        if not machine.advance(target, slow=args.slow):
            status = "HALT"
            break
    result = machine.snapshot()
    result["status"] = status
    result["elapsed"] = time.monotonic() - start
    print(json.dumps(result), flush=True)
    if args.checkpoint is not None:
        args.checkpoint.parent.mkdir(parents=True, exist_ok=True)
        args.checkpoint.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
