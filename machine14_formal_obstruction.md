# Machine 14: formal block-model attempt and obstruction

Machine: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`.

## Result

`bbwork/lean/Machine14.lean` now compiles cleanly.  It formalizes the supplied
19-rule block abstraction, not the raw five-symbol machine.

Proved:

- `stepB_inv`: every *defined* block step preserves the partition invariant
  `Inv` (`L` remains on the left, `R` remains on the right).
- `gt_R_stuck`: the block model has no rule for a `>` head reading `R`.
- `gt_R_partition`: the stuck state nevertheless satisfies `Inv`.
- `partition_insufficient`: the supplied partition invariant alone does not
  imply that the block simulation can continue.
- `gt_R_not_avoids`: the stuck state violates the missing avoidance condition
  `AvoidsGtR`.
- `avoids_not_inductive`: `AvoidsGtR` is not itself inductive; the allowed
  context `> V R` steps to the stuck `> R` state.  A usable block invariant
  must exclude such predecessor contexts too.

`#print axioms` reports `propext` for the partition results and
`[propext, Quot.sound]` for `avoids_not_inductive`.  There is no `sorry` in the
file.

## Why this is an obstruction, not a nonhalting proof

The supplied partition says which blocks may occur on each side, but it does not
exclude the context `>` with `R` first on the right.  That context is exactly a
raw halt approach: a `>` head at the right end meeting `21$`.  A block-level
proof needs a stronger invariant `AvoidsGtR`; a raw-machine proof additionally
needs a raw-to-block simulation theorem.

The empirical bridge test
(`machine14_block_bridge_gap.py`, `machine14_block_bridge_gap.json`) covers
5,000 macro steps and all 19 rules, with boundary gaps only 0 or 1.  It does not
prove the bridge, the gap rule, or avoidance for arbitrary contexts.

A longer block-model run (`machine14_block_rules.py 1000000 --json`) completed
10^6 macro steps with `stuck:false`, 45 blocks, and no `> R` context.  This is
still finite evidence, not an avoidance proof.

## Status

The attempt found a precise machine-checked obstruction.  It is not a proof that
machine 14 halts or does not halt.
