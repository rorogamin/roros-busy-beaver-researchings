#!/usr/bin/env python3
"""Finite certificates for the two-epoch nonhalting proof.

Machine: 1RB3LA3LA0RB2LB_2LA4LA4RA2RA---
Python 3.10+, standard library only.

This program verifies the finite entry and cross-checks the exact epoch map.
It is NOT a substitute for the infinite induction in NONHALTING_PROOF.md,
and is NOT a Lean kernel verification.

Run:
    python3 verify_certificate.py
    python3 verify_certificate.py --exhaustive 9
    python3 verify_certificate.py --json certificate.json
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from typing import Optional

MACHINE = "1RB3LA3LA0RB2LB_2LA4LA4RA2RA---"
SEED_WORD = "PPPPPPFPCCCPPPCCCFFFC"  # tokens in Lean/reverse tape order
SEED_CHUNKS = "MMMMMMMBBBMMMBMSBBSSS"  # chunks in forward/deep-end order
EPSILON = Fraction(1, 8192)
R = 12
K = 8
DELTA = Fraction(3, 131072)


def require(condition: bool, message: str) -> None:
    """Do not disappear under python -O."""
    if not condition:
        raise AssertionError(message)


# Raw machine, exactly the list convention of RequestProject/Machine.lean.
TABLE = (
    ((1, 1, 1), (3, -1, 0), (3, -1, 0), (0, 1, 1), (2, -1, 1)),
    ((2, -1, 0), (4, -1, 0), (4, 1, 0), (2, 1, 0), None),
)
RawCfg = tuple[list[int], int, list[int]]


def raw_run(n: int) -> RawCfg:
    left: list[int] = []
    right: list[int] = []
    state = 0
    for time in range(n):
        transition = TABLE[state][right[0] if right else 0]
        require(transition is not None, f"Raw halt at step {time}")
        assert transition is not None  # type narrowing only
        write, direction, state = transition
        if direction == 1:
            left, right = [write] + left, right[1:]
        else:
            left, right = left[1:], [left[0] if left else 0, write] + right[1:]
    return left, state, right


def arrival(word: str, suffix: tuple[int, ...] = (3, 2)) -> RawCfg:
    cells = {"F": [2, 0], "C": [2, 1], "P": [4, 0]}
    reverse = [x for c in word for x in cells[c]] + [2, 1]
    return reverse[1:], 0, reverse[:1] + list(suffix)


# Independent token-level implementation, matching the supplied carry laws.
def capacity(word: str) -> int:
    value = 0
    for token in reversed(word):
        if token == "F":
            value = 2 * value + 1
        elif token == "C":
            value *= 2
        elif token == "P":
            value //= 2
        else:
            raise ValueError(f"Unknown token {token!r}")
    return value


def carry(d: int, word: str) -> Optional[str]:
    require(d >= 0, "Negative carry index")
    out = list(word)
    for i, token in enumerate(out):
        if token == "P":
            d += 1
        elif d:
            d -= 1
        elif token == "F":
            out[i] = "C"
            return "".join(out)
        else:
            require(token == "C", "Bad token in carry")
            out[i] = "F"
    return None


def decoration(word: str) -> str:
    """The hidden-bit refinement D, valid at every capacity."""
    value = 0
    result: list[str] = []
    for token in reversed(word):
        if token == "P":
            result.append("S" if value % 2 else "B")
            value //= 2
        elif token == "F":
            result.append("M")
            value = 2 * value + 1
        elif token == "C":
            result.append("M")
            value *= 2
        else:
            raise ValueError(f"Unknown token {token!r}")
    return "".join(result)


def chunks(word: str) -> str:
    require(capacity(word) == 0, "chunks requires an overflow word")
    out: list[str] = []
    while word:
        token, word = word[0], word[1:]
        require(token != "F", "A zero-capacity recursion encountered F")
        if token == "C":
            out.append("M")
        else:
            require(token == "P", "Bad token in chunks")
            changed = carry(0, word)
            if changed is None:
                out.append("B")
            else:
                out.append("S")
                word = changed
    return "".join(reversed(out))


def rebuild_cells(cells: str) -> str:
    """The original pair-of-cells recursion, not the new chunk transducer."""
    word = ""
    i = 0
    while i + 1 < len(cells):
        x, y = cells[i:i + 2]
        i += 2
        require(x in "23" and y in "23", "Non-spill cell")
        if x == "2":
            changed = carry(0, word)
            require(changed is not None, "Overflow inside the rebuild")
            assert changed is not None
            word = changed
        word = ("F" if y == "3" else "P") + word
    require(i < len(cells), "Expected odd-length rebuild")
    if cells[i] == "2":
        changed = carry(0, word)
        require(changed is not None, "Last rebuild carry failed")
        assert changed is not None
        word = changed
    else:
        require(cells[i] == "3", "Bad final cell")
    return word


@dataclass(frozen=True)
class Run:
    value: int
    emitted: str
    conversions: int


def scan(cs: str) -> Optional[Run]:
    value = 0
    emitted: list[str] = []
    conversions = 0
    for c in cs:
        if c == "M":
            emitted.append("M")
            value = 2 * value + 1
        elif c == "S":
            emitted.append("M")
            value *= 2
        elif c == "B":
            if value < 2:
                return None
            bit = value % 2
            emitted.append("S" if bit else "B")
            conversions += bit
            value = value // 2 - 1
        else:
            raise ValueError(f"Unknown chunk {c!r}")
    return Run(value, "".join(emitted), conversions)


def epoch(cs: str) -> str:
    result = scan(cs)
    require(result is not None and result.value >= 3, "Epoch outside its domain")
    assert result is not None
    number = result.value + 5
    t = number.bit_length() - 1
    bits = "".join("S" if (number >> j) & 1 else "B" for j in range(t))
    return result.emitted + bits


def token_epoch(word: str) -> tuple[str, int]:
    """One epoch via the existing spill, rebuild, tail and pass laws."""
    cs = chunks(word)
    result = scan(cs)
    require(result is not None and result.value >= 3, "Bad finite epoch")
    assert result is not None
    syms = {"M": "33", "S": "32", "B": "22"}
    full = rebuild_cells("3" + "".join(syms[c] for c in cs) + "32")
    require(full.startswith("C"), "Rebuild does not end with the charged marker")
    require(capacity(full) == 2 * result.value, "Wrong final rebuild capacity")
    u = full[1:]
    require(capacity(u) == result.value, "Wrong core capacity")
    # The tail-eating carry costs 1; the following carry through 22 costs 2.
    u1 = carry(0, u)
    require(u1 is not None, "Tail-eating carry failed")
    assert u1 is not None
    u2 = carry(1, u1)
    require(u2 is not None, "Post-tail carry failed")
    assert u2 is not None
    current = "PPP" + u2
    t = 3
    while True:
        changed = carry(0, current)
        if changed is None:
            break
        current = "P" + changed
        t += 1
    number = result.value + 5
    require(t == number.bit_length() - 1, "Pass count formula failed")
    require(capacity(current[t:]) == number - (1 << t), "Residual capacity failed")
    require(len(current) == len(word) + t, "Word length formula failed")
    require(chunks(current) == epoch(cs), "New transducer disagrees with token laws")
    return current, t


def inverse_power(height: int) -> Fraction:
    return Fraction(1, 1 << height) if height >= 0 else Fraction(1 << -height)


def prices(cs: str) -> tuple[int, Fraction, Fraction, int, int]:
    height = 0
    price = Fraction(0)
    paying_heights: list[int] = []
    for c in cs:
        height += -1 if c == "B" else 1
        if c != "M":
            price += inverse_power(height)
            paying_heights.append(height)
    terminal = inverse_power(height)
    return height, price, terminal, min(paying_heights + [height]), len(paying_heights)


def record(n: int, word: str) -> dict:
    cs = chunks(word)
    result = scan(cs)
    require(result is not None, "Recorded epoch has a failed scan")
    assert result is not None
    e, p, terminal, minimum, count = prices(cs)
    phi = p + terminal
    return {
        "overflow": n,
        "token_word_reverse_tape_order": word,
        "chunks_deep_end_first": cs,
        "length": len(cs),
        "height": e,
        "minimum_paying_or_terminal_height": minimum,
        "paying_chunks": count,
        "trailing_S": len(cs) - len(cs.rstrip("S")),
        "conversions": result.conversions,
        "fold_capacity": str(result.value),
        "phi_numerator": str(phi.numerator),
        "phi_denominator": str(phi.denominator),
    }


def verify_finite() -> dict:
    require(raw_run(4011) == arrival(SEED_WORD), "Raw blank-to-seed check failed")
    require(capacity(SEED_WORD) == 0, "Seed is not an overflow")
    require(chunks(SEED_WORD) == SEED_CHUNKS, "Wrong seed chunks")
    word = SEED_WORD
    records: list[dict] = []
    words: dict[int, str] = {}
    for n in range(5, 15):
        rec = record(n, word)
        records.append(rec)
        words[n] = rec["chunks_deep_end_first"]
        print(f"overflow {n:2}: length={rec['length']:4}, height={rec['height']:4}, "
              f"paying/terminal depth>={rec['minimum_paying_or_terminal_height']:3}, "
              f"trailing S={rec['trailing_S']:3}, conversions={rec['conversions']:3}")
        if n < 14:
            word, _ = token_epoch(word)
    for n in (12, 13):
        cs = words[n]
        result = scan(cs)
        assert result is not None
        e, p, terminal, minimum, count = prices(cs)
        require(p + terminal <= EPSILON, f"Price certificate {n} failed")
        require(cs.endswith("S" * R), f"Suffix certificate {n} failed")
        require(result.conversions >= K, f"Conversion certificate {n} failed")
        require(Fraction(count + 1) * inverse_power(minimum) <= EPSILON,
                f"Coarse integer-only price certificate {n} failed")
    require(epoch(words[12]) == words[13], "Base words are not successive")
    # One finite instance of the proved two-epoch bound (a consistency check).
    p12 = prices(words[12])[1]
    phi14 = sum(prices(words[14])[1:3], Fraction(0))
    require(phi14 <= p12 / 4 + 2 * DELTA, "Two-epoch bound instance failed")
    require(EPSILON / 4 + 2 * DELTA == 5 * EPSILON / 8, "Closing constants failed")
    print("PASS: raw entry, token/chunk cross-checks, and the two base certificates.")
    return {
        "machine": MACHINE,
        "verification_status": "Python exact finite checks; not Lean kernel verification",
        "raw_entry_steps": 4011,
        "seed_overflow": 5,
        "base_pair": [12, 13],
        "r": R,
        "minimum_conversions": K,
        "epsilon": "1/8192",
        "suffix_cost_bound": "3/131072",
        "records": records,
    }


def exhaustive(max_length: int) -> None:
    require(0 <= max_length <= 12, "Use an exhaustive length between 0 and 12")
    count = 0
    for length in range(max_length + 1):
        for letters in product("MSB", repeat=length):
            cs = "".join(letters)
            one = scan(cs)
            if one is None:
                continue
            two = scan(one.emitted)
            require(two is not None, "Domination failed")
            assert two is not None
            p0 = prices(cs)[1]
            p1 = prices(one.emitted)[1]
            p2 = prices(two.emitted)[1]
            require(p1 <= p0, "One-step inherited price bound failed")
            require(p2 <= p0 / 4, "Two-step inherited price bound failed")
            syms = {"M": "33", "S": "32", "B": "22"}
            rebuilt = rebuild_cells("3" + "".join(syms[c] for c in cs) + "32")
            require(rebuilt.startswith("C"), "Missing final charged marker")
            require(capacity(rebuilt[1:]) == one.value, "Rebuild scan value failed")
            require(decoration(rebuilt[1:]) == one.emitted,
                    "Hidden-bit rebuild emission lemma failed")
            count += 1
    print(f"PASS: inherited-price inequalities and exact rebuild emission for {count} "
          f"successful words of length at most {max_length} "
          "(diagnostic, not an infinite proof).")
    token_count = 0
    carry_count = 0
    for length in range(max_length + 1):
        for letters in product("FCP", repeat=length):
            word = "".join(letters)
            cap = capacity(word)
            dec = decoration(word)
            if cap == 0:
                require(chunks(word) == dec, "Zero-capacity decoration lemma failed")
            for d in range(max_length + 1):
                changed = carry(d, word)
                if changed is not None:
                    require(capacity(changed) == cap - (1 << d),
                            "Carry-capacity correspondence failed")
                    require(decoration(changed) == dec,
                            "Carry-invariant decoration lemma failed")
                    carry_count += 1
                else:
                    require(cap < (1 << d), "Carry failure criterion failed")
            token_count += 1
    print(f"PASS: hidden-bit decoration on {token_count} token words and "
          f"{carry_count} successful carries (finite diagnostic).")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the exact finite certificate")
    parser.add_argument("--exhaustive", type=int, help="optional small-word diagnostics")
    args = parser.parse_args()
    certificate = verify_finite()
    if args.exhaustive is not None:
        exhaustive(args.exhaustive)
    if args.json is not None:
        args.json.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {args.json}")


if __name__ == "__main__":
    main()
