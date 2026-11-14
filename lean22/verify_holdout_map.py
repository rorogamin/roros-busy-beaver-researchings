#!/usr/bin/env python3
"""Check the 20 nonhalting Lean claims against the 60-machine holdout list.

The two halting claims are excluded.  One proof (#32) uses the left-right
mirror of the official machine; reflection preserves halting, so we check that
exactly instead of pretending the string is identical.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read_list(path: Path) -> list[str]:
    """Read machine strings, ignoring provenance headers and blank lines."""
    return [
        line.strip()
        for line in path.read_text().splitlines()
        if line.strip().startswith("1RB") and "_" in line
    ]


def mirror(machine: str) -> str:
    rows = []
    for row in machine.split("_"):
        cells = []
        for i in range(0, len(row), 3):
            cell = row[i:i + 3]
            if cell == "---":
                cells.append(cell)
            else:
                write, move, nxt = cell
                cells.append(write + ("R" if move == "L" else "L") + nxt)
        rows.append("".join(cells))
    return "_".join(rows)


def main() -> None:
    official = read_list(ROOT / "BB2x5_Rocq_holdouts_60.txt")
    formal37 = read_list(ROOT / "bb2x5_holdouts37.txt")
    claimed = read_list(ROOT / "solved22.txt")
    nonhalting = claimed[2:]
    assert len(nonhalting) == 20, len(nonhalting)

    official_set = set(official)
    formal_set = set(formal37)
    missing = [m for m in nonhalting if m not in official_set]
    print(f"60-list entries: {len(official)}")
    print(f"37-list entries: {len(formal37)}")
    print(f"nonhalting claims: {len(nonhalting)}")
    print(f"claims in 60-list: {len(nonhalting) - len(missing)}/{len(nonhalting)}")
    if missing:
        print("MISSING FROM 60-LIST:")
        for m in missing:
            print(" ", m)
    print(f"claims in 37-list: {sum(m in formal_set for m in nonhalting)}/{len(nonhalting)}")

    # #32's Lean statement is the mirror image of the official holdout.
    proof32 = "1LB3RB0LB---2RB_2RA3LA4LB2LB0RA"
    official32 = "1RB3LB0RB---2LB_2LA3RA4RB2RB0LA"
    print(f"#32 official string present: {official32 in official_set}")
    print(f"#32 proof string present:    {proof32 in official_set}")
    print(f"#32 mirror equals official:  {mirror(proof32) == official32}")
    print(f"#32 mirror:                  {mirror(proof32)}")


if __name__ == "__main__":
    main()
