#!/usr/bin/env python3
"""Identity check for the 21-state omega^2 row in rocq/Machine21Base.v.

The Rocq theorem [table21_rows] proves that the literal table has the rows in
[champion_rows].  This script independently decodes the champion string and
checks that [champion_rows] is exactly that decoded data.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MACHINE = "0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR"


def parse_machine(text: str):
    tokens = text.split("_")
    if len(tokens) != 21:
        raise SystemExit(f"expected 21 state rows, got {len(tokens)}")
    rows = []
    for state, token in enumerate(tokens):
        if len(token) != 6:
            raise SystemExit(f"state {state}: malformed row {token!r}")
        values = []
        for offset in (0, 3):
            write = int(token[offset])
            move = 1 if token[offset + 1] == "R" else 0
            nxt = token[offset + 2]
            if nxt == "Z":
                q = 21
            else:
                q = ord(nxt) - ord("A")
            values.append((write, move, q))
        (w0, d0, q0), (w1, d1, q1) = values
        rows.append((state, w0, d0, q0, w1, d1, q1))
    return rows


def read_rocq_rows():
    source = (ROOT / "rocq" / "Machine21Base.v").read_text(encoding="utf-8")
    match = re.search(
        r"Definition champion_rows : list row_code := \[(.*?)\n\]\.",
        source,
        re.S,
    )
    if not match:
        raise SystemExit("champion_rows list not found in Machine21Base.v")
    field = re.compile(
        r"r_state := (\d+); r_w0 := (\d+); r_d0 := (\d+); r_q0 := (\d+); "
        r"r_w1 := (\d+); r_d1 := (\d+); r_q1 := (\d+)"
    )
    rows = []
    for line in match.group(1).splitlines():
        found = field.search(line)
        if found:
            rows.append(tuple(int(x) for x in found.groups()))
    return rows


def main():
    decoded = parse_machine(MACHINE)
    recorded = read_rocq_rows()
    if decoded != recorded:
        for i, (a, b) in enumerate(zip(decoded, recorded)):
            if a != b:
                print(f"row {i}: string {a} != Rocq {b}")
        print(f"row count: string {len(decoded)}, Rocq {len(recorded)}")
        return 1

    halts = [(s, sym) for s, *rest in decoded for sym, q in enumerate((rest[2], rest[5])) if q == 21]
    if halts != [(17, 0)]:
        print(f"expected the single halt row (17, 0), got {halts}")
        return 1
    if [row[0] for row in decoded] != list(range(21)):
        print("state rows are not 0..20 in order")
        return 1
    print("TABLE IDENTITY OK: 21 rows; single halt at state 17, read 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
