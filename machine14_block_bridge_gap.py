#!/usr/bin/env python3
"""Gap-aware raw-to-block bridge check for machine 14 (BB(2,5)).

The block model in machine14_block_rules.py has no explicit blank cells.
Raw runs can leave a 0 cell at the head boundary, so this checker tests the
explicit encoding

    raw = enc(left blocks) + 0**gap + enc(right blocks),  gap in {0,1,2}

with the head at the last cell of the left block for '<', and at the first
cell of the right block for '>' and 'w>'.  '<' and '>' are state A; 'w>' is
state B.

The raw machine is started at the configuration reached after 14 ordinary
steps, which is exactly L U Q < R with gap 0.  Each block step is checked
against a bounded raw simulation.  The script fails if the raw endpoint is
not unique or does not match exactly.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

import bb
import machine14_block_rules as blocks

MACHINE = "1RB2LA0RB4LB1RA_1LA3RA1RA---0LA"

ENC = {
    "L": "11",
    "R": "1",
    "X": "142",
    "Y": "031",
    "U": "01",
    "W": "11",
    "V": "22",
    "C": "14",
    "F": "03",
    "C1": "24",
    "C2": "21",
    "P": "2",
    "Q": "1",
}

ALL_RULES = {
    ("<", "W"),
    ("<", "U"),
    ("<", "L"),
    ("<", "Y"),
    ("<", "F"),
    ("<", "Q"),
    (">", "V"),
    (">", "X"),
    (">", "C"),
    (">", "C1"),
    (">", "C2"),
    (">", "P"),
    ("w>", "V"),
    ("w>", "X"),
    ("w>", "R"),
    ("w>", "C"),
    ("w>", "C1"),
    ("w>", "C2"),
    ("w>", "P"),
}


def encode(tokens: list[str]) -> str:
    return "".join(ENC[t] for t in tokens)


def snapshot(tape: dict[int, int], head: int) -> tuple[str, int]:
    if tape:
        lo, hi = min(tape), max(tape)
    else:
        lo = hi = head
    return "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1)), head - lo


def expected(tokens: list[str], h: int, bhead: str, gap: int) -> tuple[str, int, int]:
    left = encode(tokens[:h])
    right = encode(tokens[h:])
    if bhead == "<":
        off = len(left) - 1
        state = 0
    else:
        off = len(left) + gap
        state = 0 if bhead == ">" else 1
    return left + "0" * gap + right, off, state


def advance_to(
    tape: dict[int, int],
    head: int,
    state: int,
    want: str,
    off: int,
    want_state: int,
    limit: int,
) -> tuple[bool, dict[int, int], int, int, int]:
    for k in range(limit):
        got, got_off = snapshot(tape, head)
        if got == want and got_off == off and state == want_state:
            return True, tape, head, state, k
        tr = TM.trans[state][tape.get(head, 0)]
        if tr is None:
            return False, tape, head, state, k
        write, direction, nxt = tr
        if write:
            tape[head] = write
        else:
            tape.pop(head, None)
        head += direction
        state = nxt
    return False, tape, head, state, limit


def start_raw() -> tuple[dict[int, int], int, int]:
    tape: dict[int, int] = {}
    head = 0
    state = 0
    for _ in range(14):
        tr = TM.trans[state][tape.get(head, 0)]
        if tr is None:
            raise RuntimeError("machine 14 halts in the 14-step prefix")
        write, direction, nxt = tr
        if write:
            tape[head] = write
        else:
            tape.pop(head, None)
        head += direction
        state = nxt
    return tape, head, state


TM = bb.TM.parse(MACHINE)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=5_000, help="block steps to check")
    parser.add_argument("--json", type=Path, default=Path(__file__).with_name("machine14_block_bridge_gap.json"))
    parser.add_argument("--limit", type=int, default=500, help="raw-step limit per macro")
    args = parser.parse_args()

    tape, raw_head, raw_state = start_raw()
    tokens = ["L", "U", "Q", "R"]
    h = 3
    bhead = "<"
    gap = 0
    raw_steps = 0
    rule_counts: Counter[tuple[str, str]] = Counter()
    gap_counts: Counter[int] = Counter()
    max_macro = 0
    max_macro_at = -1

    raw14, raw14_off = snapshot(tape, raw_head)
    init_want, init_off, init_state = expected(tokens, h, bhead, gap)
    if (raw14, raw14_off, raw_state) != (init_want, init_off, init_state):
        print("initial mismatch:", raw14, raw14_off, raw_state, "wanted", init_want, init_off, init_state)
        return 1

    for i in range(args.steps):
        want, off, want_state = expected(tokens, h, bhead, gap)
        got, got_off = snapshot(tape, raw_head)
        if (got, got_off, raw_state) != (want, off, want_state):
            print(f"state mismatch before block step {i}: raw={got!r}/{got_off}/{raw_state} want={want!r}/{off}/{want_state}")
            return 1

        rule = (bhead, tokens[h - 1] if bhead == "<" else tokens[h])
        rule_counts[rule] += 1
        result = blocks.step(tokens, h, bhead)
        if result is None:
            print(f"block model stuck at step {i}: {bhead=} {h=} {tokens=}")
            return 1
        nt, nh, nbhead = result

        matches = []
        for g in (0, 1, 2):
            w2, o2, s2 = expected(nt, nh, nbhead, g)
            ok, t2, r2, st2, used = advance_to(
                dict(tape), raw_head, raw_state, w2, o2, s2, args.limit
            )
            if ok:
                matches.append((g, t2, r2, st2, used))
        if len(matches) != 1:
            print(f"non-unique/failed raw endpoint at block step {i}: {[m[0] for m in matches]}")
            print("input:", bhead, h, " ".join(tokens[:h]), "|", " ".join(tokens[h:]))
            print("output:", nbhead, nh, " ".join(nt[:nh]), "|", " ".join(nt[nh:]))
            return 1

        g, t2, r2, st2, used = matches[0]
        raw_steps += used
        gap_counts[g] += 1
        if used > max_macro:
            max_macro, max_macro_at = used, i
        tape, raw_head, raw_state = t2, r2, st2
        tokens, h, bhead, gap = nt, nh, nbhead, g

    missing = sorted(ALL_RULES - set(rule_counts))
    extra = sorted(set(rule_counts) - ALL_RULES)
    summary = {
        "machine": MACHINE,
        "raw_start": {"after_steps": 14, "tape": raw14, "head_offset": raw14_off, "state": raw_state},
        "block_steps": args.steps,
        "raw_steps": raw_steps,
        "initial_tokens": ["L", "U", "Q", "R"],
        "gap_counts": {str(k): v for k, v in sorted(gap_counts.items())},
        "rule_counts": {f"{h}:{t}": v for (h, t), v in sorted(rule_counts.items())},
        "rules_seen": len(rule_counts),
        "rules_expected": len(ALL_RULES),
        "missing_rules": missing,
        "extra_rules": extra,
        "max_raw_steps_per_macro": max_macro,
        "max_raw_steps_at_block_step": max_macro_at,
        "final_tokens": tokens,
        "final_h": h,
        "final_head": bhead,
        "final_gap": gap,
    }
    args.json.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if missing or extra:
        print("rule coverage failure")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
