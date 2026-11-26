"""Ladder Tag (LT) -- an ATS variant tuned for long runs from short tapes.

LT is the Absorbing Tag System with the same tape language, absorption phase,
length convention and halting rule (`fn(...)` wrapper free, halt when the tape
empties -- see ../ATS/README.md).  Two head rules differ, both chosen to raise
the number of steps a short tape survives:

  * a `1` head appends copies of the next THREE tokens (ATS: two), so every
    growth step adds two tokens instead of one;
  * the zero-rule pops the tail token and appends `fn(0)` -- a "cinder" that
    must still be carried to the head and popped, so draining the queue costs
    about two steps per token instead of one.

The cinder is the important half: paying back real fuel (`fn(1)`) instead makes
tapes explode without halting (no length-n tape below n=5 halted above 25
steps, and the search drowns in tokencap hits), so the variant hands back a
token that costs a step but cannot grow.

Token representation follows ../ATS/ats.py: primitives are ints 0/1, function
tokens are strings, so `fn(0)` is "0" and `fn(1)` is "1".

    python lt.py sim "[1, 1, fn(0)]" --max-steps 1000
    python lt.py search --max-n 6 --step-limit 100000
"""

from __future__ import annotations

import argparse
import itertools
import sys
from dataclasses import dataclass, field

COPY_K = 3
CINDER = "0"  # fn(0): costs a step at the head, cannot grow the tape


def is_fn(t) -> bool:
    return isinstance(t, str)


def tok_len(t) -> int:
    return 1 if not isinstance(t, str) else len(t)


def tape_length(tape) -> int:
    return sum(tok_len(t) for t in tape)


def count_zeros(tape) -> int:
    n = 0
    for t in tape:
        n += t.count("0") if isinstance(t, str) else (1 if t == 0 else 0)
    return n


def format_tape(tape) -> str:
    out = []
    for t in tape:
        out.append("fn(%s)" % t if isinstance(t, str) else str(t))
    return "[" + ", ".join(out) + "]"


def parse_tape(text: str) -> list:
    text = text.strip().strip("[]")
    tape = []
    for raw in text.replace(",", " ").split():
        raw = raw.strip()
        if raw.startswith("fn(") and raw.endswith(")"):
            tape.append(raw[3:-1])
        elif raw in ("0", "1"):
            tape.append(int(raw))
        else:
            raise ValueError("bad token %r" % raw)
    return tape


def absorption_phase(tape):
    """ATS absorption: an internal function folds in the primitive on its right."""
    j = 1
    while j < len(tape) - 1:
        if is_fn(tape[j]) and not is_fn(tape[j + 1]):
            tape[j] = str(tape[j + 1]) + tape[j]
            del tape[j + 1]
            continue
        j += 1


def _one_rule(tape, alpha: str) -> None:
    """ATS one-rule: append fn(1), then fn(rest) if non-empty."""
    idx = alpha.find("1")
    rest = alpha[:idx] + alpha[idx + 1:] if len(alpha) > 3 else alpha[1:]
    tape.append("1")
    if rest:
        tape.append(rest)


def _zero_rule(tape) -> None:
    """LT zero-rule: spend the tail token, leave a cinder behind."""
    if tape:
        tape.pop()
    tape.append(CINDER)


def execution_phase(tape) -> None:
    head = tape.pop(0)

    if head == 0:
        return
    if head == 1:
        tape.extend(tape[:COPY_K])
        return

    alpha = head
    c0 = alpha.count("0")
    c1 = alpha.count("1")
    if c1 == 0:          # pure zeros: a lone 0
        return
    if alpha == "1":     # fn(1): a primitive 1
        tape.extend(tape[:COPY_K])
        return

    if c0 == 0:
        _one_rule(tape, alpha)
    elif c1 > c0 or (c1 == c0 and alpha[0] == "1"):
        _one_rule(tape, alpha)
        _zero_rule(tape)
    else:
        _zero_rule(tape)
        _one_rule(tape, alpha)


@dataclass
class Result:
    steps: int
    halted: bool
    reason: str
    peak_tokens: int = 0
    peak_len: int = 0
    final: list = field(default_factory=list)


def simulate(initial, *, max_steps=100_000, max_tokens=100_000,
             detect_cycles=True, zero_free=True, trace=0, out=sys.stdout):
    tape = list(initial)
    steps = 0
    seen = set()
    peak_tok = len(tape)
    peak_len = tape_length(tape)

    while tape:
        if steps >= max_steps:
            return Result(steps, False, "max-steps", peak_tok, peak_len, tape)
        if len(tape) > max_tokens:
            return Result(steps, False, "token-limit", peak_tok, peak_len, tape)
        # The zero-free decider only prunes, so it may be sampled: checking it
        # every 256 steps keeps long runs affordable without changing any
        # verdict (a zero-free tape is still reported, just a few steps later).
        if zero_free and steps % 256 == 0 and len(tape) >= 2 and count_zeros(tape) == 0:
            return Result(steps, False, "zero-free", peak_tok, peak_len, tape)
        if detect_cycles:
            key = tuple(tape)
            if key in seen:
                return Result(steps, False, "cycle", peak_tok, peak_len, tape)
            seen.add(key)
        if steps < trace:
            print("%8d  %s" % (steps, format_tape(tape)), file=out)
        absorption_phase(tape)
        execution_phase(tape)
        steps += 1
        peak_tok = max(peak_tok, len(tape))
        peak_len = max(peak_len, tape_length(tape))

    return Result(steps, True, "halted", peak_tok, peak_len, tape)


def partitions(n):
    yield (n,)
    for first in range(1, n):
        for rest in partitions(n - first):
            yield (first,) + rest


def candidates(n):
    for part in partitions(n):
        choices = []
        for k in part:
            if k == 1:
                choices.append([0, 1, "0", "1"])
            else:
                choices.append(["".join(b) for b in itertools.product("01", repeat=k)])
        for cand in itertools.product(*choices):
            yield list(cand)


def search(max_n, step_limit, token_limit):
    for n in range(1, max_n + 1):
        best = (-1, None)
        halters = 0
        total = 0
        limited = 0
        for cand in candidates(n):
            total += 1
            r = simulate(cand, max_steps=step_limit, max_tokens=token_limit)
            if r.halted:
                halters += 1
                if r.steps > best[0]:
                    best = (r.steps, list(cand), r.peak_tokens, r.peak_len)
            elif r.reason in ("token-limit", "max-steps"):
                limited += 1
        print(
            "length %d: %d steps %s  (%d/%d halted, %d unresolved, peak %d tok / %d len)"
            % (n, best[0], format_tape(best[1]) if best[1] else "-", halters, total,
               limited, best[2], best[3])
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sim")
    s.add_argument("tape")
    s.add_argument("--max-steps", type=int, default=100_000)
    s.add_argument("--max-tokens", type=int, default=100_000)
    s.add_argument("--trace", type=int, default=0)
    q = sub.add_parser("search")
    q.add_argument("--max-n", type=int, default=6)
    q.add_argument("--step-limit", type=int, default=100_000)
    q.add_argument("--token-limit", type=int, default=2000)
    args = ap.parse_args()

    if args.cmd == "sim":
        r = simulate(parse_tape(args.tape), max_steps=args.max_steps,
                     max_tokens=args.max_tokens, trace=args.trace)
        print("result: %s; steps=%d; halted=%s; peak_tokens=%d; peak_len=%d"
              % (r.reason, r.steps, r.halted, r.peak_tokens, r.peak_len))
        print("final: " + format_tape(r.final))
    else:
        search(args.max_n, args.step_limit, args.token_limit)


if __name__ == "__main__":
    main()
