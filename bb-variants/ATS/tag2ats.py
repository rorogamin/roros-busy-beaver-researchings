#!/usr/bin/env python3
"""2-tag reference, a length-five ATS gadget, and a compiler search.

The reference half is exact.  The compilation half does three things:

1.  Proves that no *uniform one-token* encoding of this tag system can work.
    The proof is structural, not a simulation cutoff.
2.  Verifies the positive fact that the length-five production itself is
    realizable: two copies of ``fn(11)`` reach five ``fn(1)`` tokens in three
    ATS steps.
3.  Exhaustively searches a bounded class of block encodings (one- and
    two-token blocks over a stated token alphabet, with per-symbol schedules).
    A candidate is accepted only if the whole tag word matches at every step.

The search is labelled with its exact class and limits.  A negative result is
not advertised as a universal impossibility for arbitrary stateful encodings.

Usage:
    py -3 tag2ats.py tag --steps 120
    py -3 tag2ats.py compile
    py -3 tag2ats.py search --block-length 2
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time
from dataclasses import dataclass
from typing import Iterable, Sequence

import ats


@dataclass(frozen=True)
class TagSystem:
    """Deterministic 2-tag system (Post convention)."""

    rules: dict[str, str]
    start: str

    def step(self, word: str) -> str | None:
        """Return the next word, or None when len(word) < 2 (halt)."""
        if len(word) < 2:
            return None
        head = word[0]
        if head not in self.rules:
            raise KeyError(f"no production for tag symbol {head!r}")
        return word[2:] + self.rules[head]

    def word_after(self, word: str, steps: int) -> str:
        for _ in range(steps):
            nxt = self.step(word)
            if nxt is None:
                return ""
            word = nxt
        return word


# realsheepthe's size-11 Post tag cryptid.  The compressed rule notation
# 11111_20_1 assigns the productions to symbols 0, 1, 2 in order.
CRYPTID = TagSystem({"0": "11111", "1": "20", "2": "1"}, "00")


def run_tag(word: str, steps: int) -> Iterable[tuple[int, str, str | None]]:
    """Yield (step, before, head) for each step; stop on halt."""
    for i in range(steps):
        if len(word) < 2:
            return
        yield i, word, word[0]
        nxt = CRYPTID.step(word)
        if nxt is None:
            return
        word = nxt


def tag_trace(limit: int) -> list[tuple[int, str, str]]:
    """Return macro checkpoints where the word is 1^n."""
    word = CRYPTID.start
    out: list[tuple[int, str, str]] = []
    for i in range(limit):
        if word and set(word) == {"1"}:
            out.append((i, word, str(len(word))))
        nxt = CRYPTID.step(word)
        if nxt is None:
            break
        word = nxt
    return out


def verify_recurrence(limit: int = 12) -> None:
    """Check the tag orbit against the published S(n) recurrence.

    S(n) = 1^n
    S(2k+2) --(2k+2)--> S(k+1)
    S(2k+3) --(2k+4)--> S(5k+9)
    """
    word = CRYPTID.start
    # 00 --(1)--> S(5)
    assert CRYPTID.step(word) == "11111"
    n = 5
    steps = 1
    checked = 0
    while checked < limit and n >= 2:
        if n % 2 == 0:
            k = n // 2 - 1
            expected_n = k + 1
            expected_steps = 2 * k + 2
        else:
            k = (n - 3) // 2
            expected_n = 5 * k + 9
            expected_steps = 2 * k + 4
        before = "1" * n
        after = CRYPTID.word_after(before, expected_steps)
        if after != "1" * expected_n:
            raise AssertionError(
                f"S({n}) after {expected_steps} steps = {after[:30]!r}, "
                f"expected 1^{expected_n}"
            )
        n = expected_n
        steps += expected_steps
        checked += 1
    print(f"tag recurrence checked: {checked} macro transitions, {steps} tag steps, n={n}")


# ---------------------------------------------------------------------------
# Positive result: the length-five production as a concrete ATS orbit
# ---------------------------------------------------------------------------

LENGTH_FIVE_GADGET: list[ats.Token] = ["11", "11"]


def verify_length_five_gadget(verbose: bool = True) -> list[ats.Token]:
    """Verify ``fn(11), fn(11) -> fn(1)^5`` in exactly three ATS steps.

    This is a real encoding of the production ``0 -> 11111``: two copies of
    the length-2 token for tag symbol 0 become five copies of the length-1
    token for tag symbol 1.  The ATS length rises from 4 to 5, matching the
    tag word length ``|11111| = 5``.
    """
    tape = list(LENGTH_FIVE_GADGET)
    if verbose:
        print("length-five gadget (ATS length 4 -> 5):")
        print(f"  step 0  len={ats.tape_length(tape):>2}  {ats.format_tape(tape)}")
    for step in range(1, 4):
        if not ats.step_ats(tape):
            raise AssertionError("gadget halted before producing 1^5")
        if verbose:
            print(
                f"  step {step}  len={ats.tape_length(tape):>2}  "
                f"{ats.format_tape(tape)}"
            )
    if tape != ["1"] * 5:
        raise AssertionError(f"gadget produced {tape!r}, expected five fn(1) tokens")
    if verbose:
        print("  verified: fn(11), fn(11) -> fn(1), fn(1), fn(1), fn(1), fn(1)")
        print("  this encodes 0 -> 11111 locally, but not the following tag steps")
    return tape


# ---------------------------------------------------------------------------
# Negative result: no uniform one-token encoding
# ---------------------------------------------------------------------------


ONE_TOKEN_NO_GO = """\
No uniform one-token encoding can simulate this tag system.

Class: each tag symbol is represented by exactly one ATS token, and a tag
word is the concatenation of its token images.  The number of ATS steps used
for a tag step may depend on the word; no fixed schedule is assumed.

Proof:
  Let V be the token image of tag symbol 1.  The first tag step is
  00 -> 11111, so the ATS orbit from two copies of E(0) must eventually be
  exactly V,V,V,V,V.

  The initial tape has only one token type.  If E(0) is a primitive, the orbit
  contains only primitives: 0 disappears, and 1 only copies itself.  If E(0)
  is a function token, the orbit contains only function tokens: the one-rule
  appends fn(1) and fn(rest), the zero-rule deletes a tail token, and no rule
  creates a primitive.  Absorption is therefore vacuous (it needs an internal
  function followed by a primitive), so the first transition cannot use it.

  In a one-type tape, a step can create a new copy of V only by
    - V being primitive 1 or fn(1), whose head copies the next two tokens; or
    - V being the fn(1) appended by a composite one-rule.
  A composite V cannot be appended as both outputs of a one-rule: one output
  is always fn(1), and the other is fn(rest); for both to equal V we need
  V = fn(1).  A pure-zero function or primitive 0 appends nothing.  Hence
  V is primitive 1 or fn(1).

  From five primitive-1/fn(1) tokens, every head is again primitive 1 or
  fn(1): it pops and copies two tokens of the same closed type set.  No
  token whose argument contains 0, and no composite token type, can ever
  appear.

  But the second tag step is 11111 -> 11120.  Its image must contain the
  images of symbols 2 and 0.  Those images cannot contain a zero-bearing
  token.  They also cannot be a third and fourth distinct token type, since
  the closed orbit only has primitive 1 and fn(1).  If E(0), E(1), E(2) are
  all chosen from those two types, the encoding is not injective and cannot
  represent the tag word.  Therefore the second tag step is impossible.

This proves impossibility for the stated one-token class.  It does not rule
out multi-token blocks, stateful encodings, or a different global encoding.
"""


# ---------------------------------------------------------------------------
# Bounded search over block encodings
# ---------------------------------------------------------------------------


def token_alphabet(max_alpha: int) -> list[ats.Token]:
    """Primitives and fn(alpha) for every nonempty alpha of length <= max_alpha."""
    alphabet: list[ats.Token] = [0, 1]
    for length in range(1, max_alpha + 1):
        for bits in itertools.product("01", repeat=length):
            alphabet.append("".join(bits))
    return alphabet


def tag_words(max_length: int) -> list[str]:
    return [
        "".join(bits)
        for length in range(2, max_length + 1)
        for bits in itertools.product("012", repeat=length)
    ]


def encode_blocks(word: str, blocks: dict[str, tuple[ats.Token, ...]]) -> list[ats.Token]:
    out: list[ats.Token] = []
    for symbol in word:
        out.extend(blocks[symbol])
    return out


def next_tag_word(word: str) -> str | None:
    return CRYPTID.step(word)


def run_ats(tape: Sequence[ats.Token], steps: int) -> list[ats.Token]:
    current = list(tape)
    for _ in range(steps):
        if not ats.step_ats(current):
            break
    return current


@dataclass
class SearchResult:
    class_name: str
    encodings_tested: int
    first_transition_candidates: int
    full_candidates: list[tuple[dict[str, tuple[ats.Token, ...]], dict[str, int]]]
    elapsed: float
    max_schedule: int
    max_word_length: int


def _find_schedule(
    blocks: dict[str, tuple[ats.Token, ...]],
    words: Sequence[str],
    max_schedule: int,
) -> dict[str, int] | None:
    """Find a per-head-symbol schedule that matches every test word exactly."""
    schedules: dict[str, int] = {}
    for head in "012":
        candidates = [w for w in words if w[0] == head]
        if not candidates:
            schedules[head] = 1
            continue
        for steps in range(1, max_schedule + 1):
            if all(
                run_ats(encode_blocks(word, blocks), steps)
                == encode_blocks(next_tag_word(word) or "", blocks)
                for word in candidates
            ):
                schedules[head] = steps
                break
        else:
            return None
    return schedules


def search_block_encodings(
    block_length: int,
    alphabet: Sequence[ats.Token],
    *,
    max_schedule: int = 8,
    max_word_length: int = 4,
    class_name: str = "block encoding",
) -> SearchResult:
    """Exhaustively test fixed-length block images with per-symbol schedules.

    Every block is exactly ``block_length`` tokens long.  The schedule for a
    tag step depends only on the head tag symbol.  Words of length
    ``2 .. max_word_length`` over {0,1,2} are tested.  A first-transition
    candidate is a mapping for which the 00 -> 11111 image is reached.
    """
    start_time = time.time()
    words = tag_words(max_word_length)
    first_transition: list[tuple[dict[str, tuple[ats.Token, ...]], int]] = []
    full: list[tuple[dict[str, tuple[ats.Token, ...]], dict[str, int]]] = []
    tested = 0

    for values in itertools.product(alphabet, repeat=3 * block_length):
        tested += 1
        blocks = {
            symbol: tuple(values[i * block_length : (i + 1) * block_length])
            for i, symbol in enumerate("012")
        }

        # Cheap necessary condition: the first tag transition must be reached.
        first_ok = None
        for steps in range(1, max_schedule + 1):
            if run_ats(encode_blocks("00", blocks), steps) == encode_blocks("11111", blocks):
                first_ok = steps
                break
        if first_ok is None:
            continue
        first_transition.append((blocks, first_ok))

        schedules = _find_schedule(blocks, words, max_schedule)
        if schedules is None:
            continue

        # Validate on longer words and then on the actual tag orbit.
        longer = tag_words(max_word_length + 2)
        extension = _find_schedule(blocks, longer, max_schedule)
        if extension is None:
            continue
        word = CRYPTID.start
        tape = encode_blocks(word, blocks)
        for _ in range(12):
            nxt = next_tag_word(word)
            if nxt is None:
                break
            tape = run_ats(tape, extension[word[0]])
            word = nxt
            if tape != encode_blocks(word, blocks):
                break
        else:
            full.append((blocks, extension))
            print(f"  candidate found: {blocks!r} schedules={extension!r}", file=sys.stderr)

    return SearchResult(
        class_name=class_name,
        encodings_tested=tested,
        first_transition_candidates=len(first_transition),
        full_candidates=full,
        elapsed=time.time() - start_time,
        max_schedule=max_schedule,
        max_word_length=max_word_length,
    )


def report_search(result: SearchResult) -> None:
    print(
        f"{result.class_name}: tested {result.encodings_tested:,} encodings, "
        f"{result.first_transition_candidates:,} reached 00 -> 11111, "
        f"{len(result.full_candidates):,} matched every test word "
        f"(schedule <= {result.max_schedule}, words <= {result.max_word_length}, "
        f"{result.elapsed:.1f}s)"
    )
    if not result.full_candidates:
        print("  no full encoding in this bounded class")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _cmd_compile(args: argparse.Namespace) -> None:
    verify_recurrence(12)

    print()
    verify_length_five_gadget()

    print()
    print(ONE_TOKEN_NO_GO.rstrip())

    print()
    if args.no_block_search:
        print("block search skipped (--no-block-search)")
        return

    one_token = search_block_encodings(
        1,
        token_alphabet(args.max_alpha),
        max_schedule=args.max_schedule,
        max_word_length=args.max_word_length,
        class_name="uniform one-token encodings",
    )
    report_search(one_token)

    # A small alphabet keeps the two-token exhaustive enumeration tractable.
    # The restriction is part of the documented search class.
    restricted = [0, 1, "0", "1", "00", "11"]
    two_token = search_block_encodings(
        2,
        restricted,
        max_schedule=args.max_schedule,
        max_word_length=args.max_word_length,
        class_name="two-token blocks over {0,1,fn(0),fn(1),fn(00),fn(11)}",
    )
    report_search(two_token)

    print()
    if one_token.full_candidates or two_token.full_candidates:
        print("a full encoding was found; inspect the candidate above")
    else:
        print(
            "no full ATS encoding was found in the searched block classes. "
            "No ATS tape for the complete tag orbit is emitted, and no ATS "
            "cryptid is certified. The one-token no-go theorem above is the "
            "only universal claim; the block search is bounded."
        )


def _cmd_search(args: argparse.Namespace) -> None:
    alphabet = (
        token_alphabet(args.max_alpha)
        if args.block_length == 1
        else [0, 1, "0", "1", "00", "11"]
    )
    result = search_block_encodings(
        args.block_length,
        alphabet,
        max_schedule=args.max_schedule,
        max_word_length=args.max_word_length,
        class_name=f"{args.block_length}-token block encodings",
    )
    report_search(result)
    for blocks, schedules in result.full_candidates:
        print("candidate", blocks, schedules)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    tag = sub.add_parser("tag", help="print tag macro checkpoints")
    tag.add_argument("--steps", type=int, default=120)

    compile_p = sub.add_parser("compile", help="prove/search the ATS compilation")
    compile_p.add_argument("--max-alpha", type=int, default=2)
    compile_p.add_argument("--max-schedule", type=int, default=8)
    compile_p.add_argument("--max-word-length", type=int, default=4)
    compile_p.add_argument("--no-block-search", action="store_true")

    search_p = sub.add_parser("search", help="run the bounded block search")
    search_p.add_argument("--block-length", type=int, default=2, choices=(1, 2))
    search_p.add_argument("--max-alpha", type=int, default=2)
    search_p.add_argument("--max-schedule", type=int, default=8)
    search_p.add_argument("--max-word-length", type=int, default=4)

    args = parser.parse_args(argv)
    if args.command == "tag":
        for step, word, n in tag_trace(args.steps):
            print(f"{step:>8}  S({n})  len={len(word)}  {word[:40]}")
        return
    if args.command == "compile":
        _cmd_compile(args)
        return
    if args.command == "search":
        _cmd_search(args)
        return
    raise AssertionError(f"unhandled command {args.command!r}")


if __name__ == "__main__":
    main()
