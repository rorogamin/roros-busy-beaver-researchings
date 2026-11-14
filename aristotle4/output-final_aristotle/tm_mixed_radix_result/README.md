# Mixed-radix attempt on the supplied 2-state, 5-symbol machine

Machine: `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`, started on the blank tape in A.

**This attempt does not decide halting or nonhalting.** It derives exact local
return-excursion rules, implements their acceleration, and reaches exactly
`10^100` transitions without finding a halt.

**Verification status:** the Python/C++ programs and their comparisons were
executed. `RequestProject/MixedRadix.lean` is an **UNCOMPILED DRAFT**, not a
checked Lean result. The `10^100` endpoint is not a Lean-certified trace.
The original project's build was not rerun here.

Read [RESULTS.md](RESULTS.md) for the proofs, limitations, and remaining goal.

## Contents

- `RequestProject/MixedRadix.lean`: proposed extension importing the original
  `RequestProject.Macro`; exact return/batch rules and rational-value theorem.
- `tools/mixed_radix.py`: Python arbitrary-precision accelerator and unit tests.
- `tools/verify.cpp`: separately coded C++ arbitrary-precision accelerator.
- `tools/check_all.py`: reproduction runner for the comparisons.
- `checkpoints/`: complete endpoints, validation metadata, and the executed
  reproduction log. Coordinates put the initial head at 0; state A is 0,
  state B is 1. The tape string spans the inclusive `lo` to `hi` coordinates;
  every other tape cell is blank.

No original source file has been modified. This is an extension package, not
a replacement for the supplied project.

## Reproduce the computations

From this directory, with Python 3.10+ and a C++17 compiler with Boost headers:

```sh
python3 tools/check_all.py
```

The runner checks random return macros, compares Python macro endpoints to a
literal million-step run, compares C++ fast/literal runs at `10^8`, and compares
both languages' full configurations at `10^100` to the stored checkpoint.
It does not run Lean.

Individual commands:

```sh
python3 tools/mixed_radix.py --test-only
python3 tools/mixed_radix.py --power 100 --checkpoint endpoint.json
g++ -std=c++17 -O3 tools/verify.cpp -o verify
./verify 100
./verify 8 slow
```

The C++ program contains a resource guard for substantially larger experiments;
check its reported `status`, not just the requested target. Python stops on an
actual halt or a storage error. Neither implementation is a general decider.

## Check the draft Lean extension

Copy `RequestProject/MixedRadix.lean` into the corresponding directory of the
original project. Keep its original `lean-toolchain`, `lakefile.toml`, and
pinned dependencies. The uploaded project specifies Lean 4.28.0 and mathlib
v4.28.0. Then run, from that original project root:

```sh
lake build
lake env lean RequestProject/MixedRadix.lean
```

These are intended verification commands, not commands successfully executed
in this environment. No Lean/lake compiler was available here. The draft has
no `sorry`, `admit`, or new axiom declarations, but that is not evidence that
it elaborates or checks. Its theorem statements only establish local macro
soundness; they do not assert `not Halts` or certify the stored long run.

## Input identity

The uploaded archive used for this attempt had SHA-256:

```text
23ecff1898c0628baf76083ab100b1ba4a0dc7931b5dcbab95f5f7fa495372ff
```
