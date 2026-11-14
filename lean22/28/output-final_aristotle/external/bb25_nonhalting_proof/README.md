# Two-epoch proof for the shift-overflow BB(2,5) machine

Machine: `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---`.

Read `NONHALTING_PROOF.md` for the complete proposed mathematical proof.
The new idea is a two-overflow contraction combined with a stable terminal
binary-digit condition. The finite base pair is overflows 12 and 13.

## Files

- `NONHALTING_PROOF.md`: the mathematical proof, including the exact epoch
  formula, all infinite-invariant lemmas, and the finite entry.
- `FORMALIZATION.md`: detailed handoff for Aristotle using the uploaded Lean
  project's definitions and existing theorems.
- `verify_certificate.py`: standard-library exact finite checker (executed).
- `certificate.json`: full finite token/chunk words and exact base data.
- `verification.log`: recorded successful checker output.
- `TwoEpochCertificate.lean`: proposed finite certificates and useful new
  computable definitions; NOT COMPILED in this environment.

## Verification status

The mathematical argument is presented as complete. Its new infinite
induction has NOT been Lean-kernel-checked here. The Python checks establish
only the stated finite calculations and consistency checks, not the infinite
conclusion by themselves. No installed Lean compiler was available.

Run:

```sh
python3 verify_certificate.py --exhaustive 9 --json certificate.json
```

The proposed Lean file is intended to be added to the original project's
`RequestProject/` directory. See `FORMALIZATION.md` before attempting the full
port; checking that finite file alone would not finish the formalization.
