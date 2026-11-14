# Mixed-counter nonhalting proof package

Machine: `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`.

## Contents

- `NONHALTING_PROOF.md`: self-contained mathematical nonhalting proof. The core result is a closed reset invariant with normalized-debt contraction by a factor of at most 3/8.
- `verify_nonhalting.py`: standard-library Python verifier for the finite bootstrap, exact mixed-counter calculations, and supplementary exhaustive tests. It does not invoke Lean.
- `VERIFICATION_REPORT.txt`: actual output of the Python checks through reset 22.
- `ARISTOTLE_HANDOFF.md`: a dependency-ordered formalization plan against the uploaded project's Lean interfaces.
- `seed_check.c`: the uploaded project's block accelerator with an additional print of the seed word, for a separate finite startup check.
- `SEED_ACCELERATOR_REPORT.txt`: actual output of that C program through reset 12.

## Run the checks

Python 3.10 or later:

```sh
python3 verify_nonhalting.py
```

For only the bootstrap and orbit checks:

```sh
python3 verify_nonhalting.py --skip-exhaustive --last-reset 22
```

Optional independent block-accelerator startup check, with GCC:

```sh
gcc -O3 seed_check.c -o seed_check
./seed_check 12 20
```

The C program uses GCC's `unsigned __int128` extension. Its second argument is a CPU-time limit; the bundled report records the successful run in this environment. Its jumps use the old clean-counter acceleration, not the newly derived whole-reset map.

## Status

The nonhalting conclusion is supported by the universal mathematical argument in `NONHALTING_PROOF.md`, not by extrapolating the finite tests. The new argument has **not** been checked by Lean, and this package does not contain a completed Lean nonhalting theorem. The original project's Lean build was not rerun here. The handoff identifies exactly which new definitions and lemmas to formalize.

Reset-body `0` and `1` denote the two-cell blocks `13` and `23`, respectively; `V` denotes `22`. Every displayed reset body has the additional implicit suffix `P Q = 2 1`.
