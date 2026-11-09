# Bigfoot (`#829`) formal snapshot

This directory is a standalone source snapshot of the Bigfoot Lean development.

## Contents

- `BusyBeaver/BB33/M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean` — the certified Collatz-like
  acceleration and the parity, four-step block, cumulative drift, and sharpness theorems.
- `BusyBeaver/Basic.lean`, `BusyBeaver/Bridge.lean`, `BusyBeaver/Defs.lean`, and
  `Cryptids/Machines.lean` — the complete local import closure of the Bigfoot module.

The snapshot was copied from the working tree at `bbwork/cryptids_a6`, a clone of
`google-deepmind/cryptids`. It contains no `.lake` build outputs.

## Build

```bash
lake exe cache get
lake build BusyBeaver.BB33.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA
```

Toolchain: `leanprover/lean4:v4.35.0-rc4`. Mathlib and Verso are external Lake dependencies.
The source tree build was verified; this copied snapshot was not re-elaborated independently.
