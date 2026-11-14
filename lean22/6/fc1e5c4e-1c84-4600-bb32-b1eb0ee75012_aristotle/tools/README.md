# Exploration tools (not verified)

Everything here is exploratory C/Python.  None of it is part of the Lean proof;
the Lean proof of halting (`BCM.halts`) recomputes what it needs with its own
verified engine.

* `transducer.py` — the cell transducer on letters `A`/`B`, and a naive
  iteration of level words.
* `crossings.py` — simulates the real machine and prints the crossing sequences
  at the cell boundaries `-3 … 4` (used to derive and check the arrival stream
  `A (BABAB)^ω` and the transducer).
* `exact.c` — exact eventually periodic words `x·y^ω` of cells `0, 1, 2, …`
  (minimal period, rotated prefix).  Usage: `./exact <cells> <capacity>`.
  Output for cells 0–170: `exact_cells_0_170.txt` (columns: cell, prefix length,
  period length, `#A`, `#B`, first letters `prefix|period`).
* `stream.c` — computes the exact word of cell `c0`, then streams it (prefix
  plus repeated periods) through the cells above, reporting the first halt.
  Usage: `./stream <c0> <capacity> <periods> <chunk>`.
  `stream165_halt.txt` is the output of `./stream 165 4000000000 40 1000000`:
  a halt at cell 238 (word `BABA`), with the heads of the words of cells
  165–238 at that moment (letter counts are only accurate to the chunk size).
* `pw_bookkeeping.c` — the periodic-word step used by the Lean engine (no
  rotation or primitive-root reduction), printing prefix/period lengths and the
  bookkeeping `a, b` (as floating point numbers).
