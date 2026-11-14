#!/usr/bin/env python3
"""Reference simulator for the Absorbing Tag System (ATS / Tagy Tag).

A tape is a list of tokens.  A token is either a primitive bit (int 0 or 1)
or a function token fn(alpha), represented here by the string alpha with
alpha non-empty.  The length convention is:

    |0| = |1| = 1
    |fn(alpha)| = len(alpha)

Each step has two phases:

1. Absorption.  Scan left to right.  A function at an internal position
   (not the first token and not the last token) absorbs a primitive bit
   immediately to its right by prepending that bit to its argument.  The
   absorbed bit is removed, and the scan continues at the same function.
   Functions absorb runs of primitive bits, stopping at the next function.

2. Head execution.  Pop the first token.
   - 0: append nothing.
   - 1: append the next two tokens (as many as exist) to the tail.
   - fn(alpha):
       * alpha has no 1: behaves as 0.
       * alpha == "1": behaves as 1.
       * otherwise it is composite:
           c0 = count("0"), c1 = count("1").
           The one-rule and zero-rule fire in an order determined by the
           counts (ties are broken by alpha[0]).
           one-rule: append fn(1) and fn(rest), where rest is alpha with
                     its first 1 removed if len(alpha) > 3, otherwise
                     alpha[1:] (drop the first character).  An empty rest
                     is not appended.
           zero-rule: pop the current last token, if any.  This rule only
                      exists when alpha contains at least one 0.

One step is one head execution.  The machine halts when the tape becomes
empty.  The empty tape has no outgoing transition.

Usage:
    python ats.py sim "1 1 1 0 fn(1) fn(1) fn(1) fn(0)" --trace 80
    python ats.py sim ... --max-steps 1000000 --trace-every 10000
    python ats.py search --max-n 7 --step-limit 100000
"""

from __future__ import annotations

import argparse
import itertools
import sys
from dataclasses import dataclass, field
from typing import Iterable, Iterator, Sequence

Token = int | str  # int is 0/1; str is the alpha of fn(alpha)


def is_fn(token: Token) -> bool:
    return isinstance(token, str)


def token_length(token: Token) -> int:
    return len(token) if is_fn(token) else 1


def tape_length(tape: Sequence[Token]) -> int:
    return sum(token_length(t) for t in tape)


def format_token(token: Token) -> str:
    return f"fn({token})" if is_fn(token) else str(token)


def format_tape(tape: Sequence[Token]) -> str:
    return "[" + ", ".join(format_token(t) for t in tape) + "]"


def format_tape_short(tape: Sequence[Token], limit: int = 60) -> str:
    if len(tape) <= limit:
        return format_tape(tape)
    half = limit // 2
    return (
        format_tape(tape[:half])[:-1]
        + f", ... {len(tape) - 2 * half} more tokens ... , "
        + format_tape(tape[-half:])[1:]
    )


def parse_token(text: str) -> Token:
    text = text.strip()
    if text in ("0", "1"):
        return int(text)
    if text.startswith("fn(") and text.endswith(")"):
        alpha = text[3:-1]
        if not alpha or any(c not in "01" for c in alpha):
            raise ValueError(f"invalid function token: {text!r}")
        return alpha
    raise ValueError(f"invalid token: {text!r}")


def parse_tape(text: str) -> list[Token]:
    text = text.strip()
    if text.startswith("[") and text.endswith("]"):
        text = text[1:-1]
    fields: list[str] = []
    current: list[str] = []
    depth = 0
    for ch in text:
        if ch == "f":
            depth += 1
        if ch == ")":
            depth -= 1
        if ch in ", " and depth == 0:
            if current:
                fields.append("".join(current))
                current = []
        else:
            current.append(ch)
    if current:
        fields.append("".join(current))
    return [parse_token(f) for f in fields]


def count_zeros(tape: Iterable[Token]) -> int:
    total = 0
    for token in tape:
        if is_fn(token):
            total += token.count("0")
        elif token == 0:
            total += 1
    return total


def _one_rule(tape: list[Token], alpha: str) -> None:
    """Append fn(1) and fn(rest) for a composite function."""
    idx = alpha.find("1")
    if len(alpha) > 3:
        rest = alpha[:idx] + alpha[idx + 1 :]
    else:
        rest = alpha[1:]
    tape.append("1")
    if rest:
        tape.append(rest)


def _zero_rule(tape: list[Token]) -> None:
    if tape:
        tape.pop()


def absorption_phase(tape: list[Token]) -> None:
    """Run the internal-absorption phase in place."""
    j = 1
    while j < len(tape) - 1:
        if is_fn(tape[j]) and not is_fn(tape[j + 1]):
            # The primitive to the right is folded into the function.
            tape[j] = str(tape[j + 1]) + tape[j]  # type: ignore[operator]
            del tape[j + 1]
            continue
        j += 1


def execution_phase(tape: list[Token]) -> None:
    """Run the head-execution phase in place.  The tape is assumed nonempty."""
    head = tape.pop(0)

    if head == 0:
        return

    if head == 1:
        tape.extend(tape[:2])
        return

    alpha = head
    c0 = alpha.count("0")
    c1 = alpha.count("1")

    if c1 == 0:  # pure zeros: acts as a lone 0
        return

    if alpha == "1":  # single one: acts as a primitive 1
        tape.extend(tape[:2])
        return

    # Composite function.
    if c0 == 0:
        # The zero-rule is disabled when the function contains no zero.
        _one_rule(tape, alpha)
    elif c1 > c0 or (c1 == c0 and alpha[0] == "1"):
        _one_rule(tape, alpha)
        if c0 > 0:
            _zero_rule(tape)
    else:
        _zero_rule(tape)
        _one_rule(tape, alpha)


def step_ats(tape: list[Token]) -> bool:
    """Perform one ATS step in place.

    Returns False if the tape was already empty (no transition), otherwise
    True.  A step counts as soon as a head token is executed.
    """
    if not tape:
        return False
    absorption_phase(tape)
    execution_phase(tape)
    return True


@dataclass
class SimulationResult:
    steps: int
    halted: bool
    reason: str
    final_tape: list[Token]
    max_tape_len: int = 0
    max_token_count: int = 0
    length_samples: list[tuple[int, int, int]] = field(default_factory=list)


def simulate(
    initial: Sequence[Token],
    *,
    max_steps: int = 1_000_000,
    detect_cycles: bool = True,
    zero_free_decider: bool = True,
    max_tape_len: int | None = None,
    sample_every: int = 0,
    trace_first: int = 0,
    trace_every: int = 0,
    out=sys.stdout,
) -> SimulationResult:
    """Simulate an initial tape.

    `reason` is one of "halted", "max-steps", "cycle", "zero-free",
    "tape-limit".  Only "halted", "cycle" and "zero-free" are proofs of
    the corresponding conclusion; "max-steps" and "tape-limit" are
    unclassified.
    """
    tape = list(initial)
    steps = 0
    seen: set[tuple[Token, ...]] = set()
    max_len = tape_length(tape)
    max_count = len(tape)
    samples: list[tuple[int, int, int]] = []

    while tape:
        current_len = tape_length(tape)
        max_len = max(max_len, current_len)
        max_count = max(max_count, len(tape))

        if max_tape_len is not None and current_len > max_tape_len:
            return SimulationResult(
                steps, False, "tape-limit", tape, max_len, max_count, samples
            )

        if zero_free_decider and count_zeros(tape) == 0 and len(tape) >= 2:
            return SimulationResult(
                steps, False, "zero-free", tape, max_len, max_count, samples
            )

        if detect_cycles:
            state = tuple(tape)
            if state in seen:
                return SimulationResult(
                    steps, False, "cycle", tape, max_len, max_count, samples
                )
            seen.add(state)

        if steps < trace_first or (trace_every and steps % trace_every == 0):
            print(
                f"{steps:>12}  len={current_len:>7}  tok={len(tape):>7}  "
                f"{format_tape(tape)}",
                file=out,
            )
        if sample_every and steps % sample_every == 0:
            samples.append((steps, current_len, len(tape)))

        if steps >= max_steps:
            return SimulationResult(
                steps, False, "max-steps", tape, max_len, max_count, samples
            )

        if not step_ats(tape):
            break
        steps += 1

    return SimulationResult(steps, True, "halted", tape, max_len, max_count, samples)


def generate_candidates(target_n: int) -> Iterator[list[Token]]:
    """Yield all tapes of ATS length `target_n`.

    A token of length k is either a primitive (k=1: 0 or 1, including their
    fn(0)/fn(1) wrappers) or an fn(alpha) with |alpha|=k.
    """

    def partitions(n: int) -> Iterator[tuple[int, ...]]:
        yield (n,)
        for first in range(1, n):
            for rest in partitions(n - first):
                yield (first,) + rest

    for partition in partitions(target_n):
        choices: list[list[Token]] = []
        for k in partition:
            if k == 1:
                choices.append([0, 1, "0", "1"])
            else:
                choices.append(
                    ["".join(bits) for bits in itertools.product("01", repeat=k)]
                )
        for candidate in itertools.product(*choices):
            yield list(candidate)


def search_champions(
    max_n: int,
    *,
    step_limit: int = 100_000,
    max_tape_len: int | None = 10_000,
) -> None:
    for n in range(1, max_n + 1):
        best_steps = -1
        best_tape: list[Token] | None = None
        halted = 0
        total = 0
        for candidate in generate_candidates(n):
            total += 1
            result = simulate(
                candidate,
                max_steps=step_limit,
                max_tape_len=max_tape_len,
                detect_cycles=True,
                zero_free_decider=True,
            )
            if result.halted:
                halted += 1
                if result.steps > best_steps:
                    best_steps = result.steps
                    best_tape = candidate
        print(
            f"length {n}: {best_steps} steps "
            f"{format_tape(best_tape) if best_tape is not None else 'None'}"
            f"  ({halted}/{total} halted)"
        )


def _cmd_sim(args: argparse.Namespace) -> None:
    tape = parse_tape(args.tape)
    result = simulate(
        tape,
        max_steps=args.max_steps,
        detect_cycles=not args.no_cycles,
        zero_free_decider=not args.no_zero_free,
        max_tape_len=args.max_tape_len,
        sample_every=args.sample_every,
        trace_first=args.trace,
        trace_every=args.trace_every,
    )
    print()
    print(
        f"result: {result.reason}; steps={result.steps}; "
        f"halted={result.halted}; final={format_tape_short(result.final_tape)}"
    )
    print(
        f"max tape length={result.max_tape_len}; "
        f"max token count={result.max_token_count}"
    )
    if result.length_samples:
        print("length samples:")
        for s, l, c in result.length_samples:
            print(f"  {s}: length={l}, tokens={c}")


def _cmd_search(args: argparse.Namespace) -> None:
    search_champions(
        args.max_n,
        step_limit=args.step_limit,
        max_tape_len=args.max_tape_len,
    )


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sim = sub.add_parser("sim", help="simulate one tape")
    sim.add_argument("tape", help='space-separated tokens, e.g. "1 1 fn(10)"')
    sim.add_argument("--max-steps", type=int, default=1_000_000)
    sim.add_argument("--max-tape-len", type=int, default=None)
    sim.add_argument("--trace", type=int, default=0, help="print first N states")
    sim.add_argument("--trace-every", type=int, default=0)
    sim.add_argument("--sample-every", type=int, default=0)
    sim.add_argument("--no-cycles", action="store_true")
    sim.add_argument("--no-zero-free", action="store_true")
    sim.set_defaults(func=_cmd_sim)

    search = sub.add_parser("search", help="search champions by ATS length")
    search.add_argument("--max-n", type=int, default=7)
    search.add_argument("--step-limit", type=int, default=100_000)
    search.add_argument("--max-tape-len", type=int, default=10_000)
    search.set_defaults(func=_cmd_search)

    args = parser.parse_args(argv)
    args.func(args)


if __name__ == "__main__":
    main()
