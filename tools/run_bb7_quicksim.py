"""Direct ground-truth simulation of all 7-state champions and holdouts using Quick_Sim.

Executes using `py -3.14` directly via Quick_Sim in `bbwork/vendor/busy-beaver/Code`.
Reports block sizes, rules proven (Levels 1-5, Iterated), power towers, and nonzeros.
Zero axioms, zero unverified claims: 100% concrete output from the simulator.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE_DIR = ROOT / "vendor" / "busy-beaver" / "Code"

MACHINES = [
    ("BB(7) 2-sym", "1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB", 20000),
    (
        "BB(7,4) seed",
        (
            "3RD1LE2RA---_0LE2LE2RB---_1RF1RC2RB---_0RC0LD3LA1LF_1RC2LE1LG0RD_0LA0LD1RZ2LF_1LD2RA2LG3RA"
        ),
        20000,
    ),
    (
        "BB(7,4) wiki",
        (
            "3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB"
        ),
        20000,
    ),
    (
        "BB(7,5)",
        (
            "2LE3LB4LC2RA4LB_4RA3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---3LF1LG4LD4LE_3RB---1LE4LE3LC_4LC------3LF3LF_3LF------1LG1LG"
        ),
        20000,
    ),
    (
        "BBi(27)",
        (
            "0LG3LB4LC2RA4LB_2LC3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---3LF---4LD4LE_3RB------4LE3LC_4LC------3LF3LF_1RB---1LG1LF---"
        ),
        20000,
    ),
    (
        "BB(7,6)",
        (
            "5LG3LB---2RA4LB0LC_4LG3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC---3RD_5RB3RE0LE4LC3LG5LE_5RB5RB2LB1LF---5LF_5LF---0LG1LG---5LG"
        ),
        20000,
    ),
]


def run_one(name, spec, loops):
  cmd = [
      "py",
      "-3.14",
      str(CODE_DIR / "Quick_Sim.py"),
      "-q",
      "--no-steps",
      f"--max-loops={loops}",
      "-r",
      "--exp-linear-rules",
      "--exp-meta-linear-rules",
      spec,
  ]
  print(f"=== Running {name} ({loops} loops) ===")
  p = subprocess.run(cmd, cwd=CODE_DIR, capture_output=True, text=True)
  lines = p.stdout.splitlines()
  for line in lines:
    if any(
        k in line
        for k in (
            "best_block_size",
            "Rules proven",
            "Level ",
            "Iterated rules",
            "Num Nonzeros",
            "Elapsed time",
            "^inf",
        )
    ):
      print(" ", line.strip())
  print()


def main():
  for name, spec, loops in MACHINES:
    run_one(name, spec, loops)


if __name__ == "__main__":
  main()
