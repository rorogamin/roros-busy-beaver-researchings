# Further progress on 1RB---3RA2LA2RB_2LB3LA4LB4RA0RA

**No blank-tape halting/nonhalting decision is claimed.**

New results: exact first-boundary-entry/overflow normal forms, extended signed
binary return digits, exact exceptional collision rules, and a mathematically
proved productive-tail family. The supplied Lean extension is an **uncompiled
draft**, not a kernel-checked certificate.

Read `RESULTS.md` for statements, proofs, and the remaining gap.

## Reproduce the executable checks

From this directory, with Python 3.10+, g++ and Boost headers:

```sh
python3 tools/check_all.py
```

This tests local rules, checks the new evaluator against literal execution,
compiles an independently coded C++ evaluator, reproduces the saved Python
prefix from blank in C++, resumes Python from that checked prefix, and compares
the entire configuration at exactly `10^1000` transitions. The Python prefix
was originally computed from blank, not guessed. Checkpointing only divides
one deterministic trajectory into two executions.

An uninterrupted Python run is available with:

```sh
python3 tools/check_all.py --full-python
```

Standalone C++ reproduction:

```sh
g++ -O3 -std=c++17 tools/verify_events.cpp -o verify_events
./verify_events 1000
```

Standalone Python reproduction:

```sh
python3 tools/event_machine.py --power 1000
```

All snapshots use initial head coordinate 0, A=0, B=1, and serialize the exact
transition count as a decimal string. `tape` lists cells from `lo` through `hi`,
inclusive. Outside the visited interval all cells are blank. Python's final
checkpoint additionally records aggregate counts across its two execution
chunks. Internal runtime paths in the resume metadata have been replaced with
relative paths for portability.

## Lean extension

Copy `RequestProject/Overflow.lean` into the supplied original project, alongside
`Machine.lean`, `Counter.lean`, and `Macro.lean`. It imports `RequestProject.Macro`.
The original project specifies Lean/mathlib 4.28.0. In that project, a checking
command is:

```sh
lake env lean RequestProject/Overflow.lean
```

No Lean compiler was available in this work environment. The draft includes
proof attempts for exact local returns and collisions, capacity arithmetic,
and productive-family return closure. It does **not** contain a proof that the
blank computation reaches that family, nor a Lean soundness proof for the full
Python/C++ event evaluators. It uses no `sorry`, `admit`, or new axioms, but this
alone does not establish successful compilation.
