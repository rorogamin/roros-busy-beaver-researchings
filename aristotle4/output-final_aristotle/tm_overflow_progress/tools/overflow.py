#!/usr/bin/env python3
"""Exact right-return and first-boundary-entry plans for the supplied TM.

These integer algorithms are mathematically justified in RESULTS.md. They are
not Lean-certified evaluators. Plans do not mutate their input. A caller must
apply edits only after accepting a complete plan.
"""
from dataclasses import dataclass
from typing import Sequence

# A=0, B=1. Entry is (written symbol, displacement, next state).
TABLE = (
    ((1, 1, 1), None, (3, 1, 0), (2, -1, 0), (2, 1, 1)),
    ((2, -1, 1), (3, -1, 0), (4, -1, 1), (4, 1, 0), (0, 1, 0)),
)
PAIR_DIGIT = {0: -1, 2: 0, 4: 1, 3: 3}
TERNARY_ENCODE = (3, 4, 0)
TERNARY_DECODE = {3: 0, 4: 1, 0: 2}

@dataclass(frozen=True)
class ReturnPlan:
    cost: int
    edits: tuple[tuple[int, int], ...]
    end: int

@dataclass(frozen=True)
class DrainPlan:
    capacity: int
    cost: int
    edits: tuple[tuple[int, int], ...]
    end: int


def return_plan(tape: Sequence[int], start: int, calls: int = 1) -> ReturnPlan | None:
    """Batch virtual A-entry/B-exit returns. Restarts are not physical steps.

    Return None when this token grammar cannot certify the requested batch.
    A failed plan changes nothing and is NOT evidence of halting.
    """
    if calls < 0:
        raise ValueError('calls must be nonnegative')
    i, k, cost = start, calls, 0
    edits: list[tuple[int, int]] = []
    while k:
        if not 0 <= i < len(tape):
            return None
        if tape[i] == 2:
            cost += 4 * k
            k *= 3
            i += 1
        elif tape[i] == 4 and i + 1 < len(tape) and tape[i + 1] in PAIR_DIGIT:
            q, bit = divmod(k + PAIR_DIGIT[tape[i + 1]], 2)
            edits.append((i + 1, 2 + 2 * bit))
            cost += 3 * k + q
            k = q
            i += 2
        else:
            return None
    return ReturnPlan(cost, tuple(edits), i)


def drain_plan(tape: Sequence[int], start: int, *, end: int | None = None) -> DrainPlan:
    """Run C completed virtual returns, then first A-entry to the chosen cut.

    If end is omitted, greedily parse until the first unsupported token.
    If end is supplied, it must be an exact token boundary; nothing at or to
    the right of end is read by this function. cost excludes outer restarts.
    """
    limit = len(tape) if end is None else end
    if not 0 <= start <= limit <= len(tape):
        raise ValueError('invalid prefix bounds')
    tokens: list[tuple[int, int | None]] = []
    i = start
    while i < limit:
        if tape[i] == 2:
            tokens.append((i, None))
            i += 1
        elif tape[i] == 4 and i + 1 < limit and tape[i + 1] in PAIR_DIGIT:
            tokens.append((i, PAIR_DIGIT[tape[i + 1]]))
            i += 2
        else:
            break
    if end is not None and i != end:
        raise ValueError('the requested prefix is not a token word')
    cap = cost = 0
    edits: list[tuple[int, int]] = []
    for pos, digit in reversed(tokens):
        child = cap
        if digit is None:
            cap, residue = divmod(child, 3)
            edits.append((pos, TERNARY_ENCODE[residue]))
            cost += 4 * cap + 1 + residue
        else:
            cap = max(0, 2 * child + 1 - digit)
            # 43 with no available child return leaves its live middle 4.
            pending = 4 if digit == 3 and child == 0 else 0
            edits.extend(((pos, 2), (pos + 1, pending)))
            cost += 3 * cap + child + 2
    return DrainPlan(cap, cost, tuple(edits), i)


def ternary_digits(value: int, width: int = 0) -> list[int]:
    """Least-significant-first digits, retaining a requested minimum width."""
    if value < 0 or width < 0:
        raise ValueError('value and width must be nonnegative')
    ds: list[int] = []
    while value:
        value, d = divmod(value, 3)
        ds.append(d)
    ds.extend([0] * max(0, width - len(ds)))
    return ds


def counter_cost(value: int, calls: int, width: int) -> int:
    """Physical cost of calls consecutive counter increments, blank on left."""
    if calls < 0 or value >= 3 ** width:
        raise ValueError('invalid initial counter or number of calls')
    old = ternary_digits(value, width)
    new = ternary_digits(value + calls, width)
    return 2 * calls + sum(old) - sum(new) + 2 * (len(new) - width)
