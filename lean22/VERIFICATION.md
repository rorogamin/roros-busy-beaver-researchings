# BB(2,5): independent verification of the 20 nonhalting claims

Date: 2026-11-07

Scope: the 20 nonhalting machines in the 22-machine prurq/Aristotle batch
(`solved22.txt`), not the two halting claims and not the separate 37-machine
formal holdout list.

## Result

All 20 nonhalting Lean developments build locally. Their final theorems were
checked with `#print axioms`.

- 18 are pure kernel results: `propext`, `Classical.choice`, `Quot.sound`
  (and for #60, only `propext`, `Quot.sound`).
- 2 use finite `native_decide` certificates: #32 and #55 also depend on
  `Lean.ofReduceBool` and `Lean.trustCompiler`.

No `sorry`, `admit`, or added `axiom` occurs in any `.lean` source.

## Machines

| Holdout | Machine | Theorem |
|---|---|---|
| #28 | `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---` | `BB25.not_halts` |
| #32 | `1RB3LB0RB---2LB_2LA3RA4RB2RB0LA` (proof uses its mirror) | `SOC.Completion.neverHalts` |
| #38 | `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---` | `TM25.machine_never_halts` |
| #40-#52 + sibling | 13-member `...4LB*` family plus `...4RB0LB` sibling | 14 `BB25.Check.not_halts_*` theorems |
| #54 | `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB` | `TM25.not_halts_init` |
| #55 | `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` | `ShiftOverflow.Counter.never_halts` |
| #60 | `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` | `BB25.never_halts` |

The 14 family theorems are stated against exact bbchallenge strings in
`40-53 family and sibling/.../RequestProject/BB25/Check.lean`. #32 is the only
non-identical statement: its proof machine is the left-right mirror of the
official #32, and `verify_holdout_map.py` checks that exact mirror relation.

## List mapping

`verify_holdout_map.py` reports:

- 20/20 verified machines are in `BB2x5_Rocq_holdouts_60.txt`.
- 0/20 are in `bb2x5_holdouts37.txt`.

So this validates 20 disputed entries in the 60-machine list. It does not
reduce the separate 37-machine formal holdout count. The two halting claims
(#6 and #12) are also outside this verification.

## Builds and checks

Builds (all exit 0):

- `28/...`: `lake build RequestProject.NonHalt` (8034 jobs)
- `55/...`: `lake build RequestProject.NoHalt` (8036 jobs)
- `40-53 family and sibling/...`: `lake build RequestProject.BB25.Check`
  (8079 jobs)
- #32, #38, #54: their default `lake build` targets completed earlier.
- #60: `lake build RequestProject.NonHalting` completed. The project's full
  default library also contains unrelated exploratory files (`Words`, `Sweeps`,
  `LeftEnd`, `CarryU21`) that fail on missing imports; none are on the final
  theorem's dependency path.

Axiom audits:

- `checks/check28.lean`, `checks/check55.lean`,
  `checks/check_family.lean` are the exact audit files.
- Logs: `check28.log`, `check55.log`, `check_family.log`.
- Family log contains all 14 results, each with
  `[propext, Classical.choice, Quot.sound]`.

The Mathlib-backed projects were built against the prebuilt Mathlib already in
`aristotle4` (same Lean v4.28.0 and rev `8f9d9cff...`), exposed through local
package junctions because the download cache was effectively stalled.
