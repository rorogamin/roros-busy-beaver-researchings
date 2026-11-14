This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA` never halts

This project contains a complete, machine-checked proof that the 2-state,
5-symbol Turing machine

```
1LB3RB0LB---2RB_2RA3LA4LB2LB0RA
```

("shift-overflow mixed-digit base (2,1.5) counter") never halts when started
from the blank tape.

The final theorem is

```lean
theorem SOC.Completion.neverHalts : SOC.NeverHalts
```

in `RequestProject/Completion.lean`, where

```lean
def SOC.NeverHalts : Prop := ∀ n, (SOC.run SOC.init n).isSome
```

`SOC.init` is the blank tape in state `A` and `SOC.step` is the transition table
above, written out literally in `RequestProject/Machine.lean`.

## Building

The development depends on **nothing but Lean 4 itself** (no Mathlib, no
Batteries):

```sh
lake build                     # builds in a few seconds
```

To inspect the final theorem and its axioms:

```lean
import RequestProject.Completion
#print axioms SOC.Completion.neverHalts
-- propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler
```

`Lean.ofReduceBool` / `Lean.trustCompiler` come from five *finite* `native_decide`
checks (compiled evaluation); see "Finite certificates" below.  Everything else
is kernel-checked.

## Module map (in dependency order)

| file | contents |
| --- | --- |
| `Machine.lean` | the machine itself: `Sym = Fin 5`, `St`, `Cfg`, `step`, `run`, `init`, `NeverHalts`, and basic run algebra |
| `Rules.lean` | the four two-cell tape rules `B> 44`, `B> 41`, `B> 40`, `B> 42`, each by `rfl` |
| `Macro.lean` | the counter alphabet `LD` (`02`, `22`, `23`, `03`), its tape encoding `lzz`, the relations `Inc` (one increment) and `Ovf` (release of the digits at an overflow), and their tape simulations |
| `MacroMachine.lean` | macro configurations `MCfg`, their encoding `enc` into tape configurations, one macro step `MStep` and its simulation |
| `Counter.lean` | `gap w`: how many increments the counter `w` still admits; `Inc.gap_eq` (an increment costs exactly one unit of gap) and `inc_exists` |
| `Safety.lean` | `BinHead` (lowest digit is radix 2) and case analysis on symbols |
| `ResetRules.lean` | `MSteps` (macro runs) and the four reset-phase block rules `44`, `04`, `24`, `14` |
| `ResetPhase.lean` | block labels `Label` and the cell expansion `cellsOf` |
| `OneSafe.lean` | `MPlus` (at least one macro step) and `plus_chain_reaches`: an infinite chain of macro steps gives an infinite run |
| `FirstPhase.lean` | `run_init_306`: after 306 steps the machine is at the start of its first reset phase, with blocks `firstBlocks` |
| `NormalPhase.lean` | the normal phase: one cycle `normal_cycle`, the overflow `normal_overflow`, and `phaseStart` |
| `Fast.lean` | the *executable* model: bulk increments `addT` (with a tail-recursive implementation registered by `@[csimp]`), the overflow `ovfF`, the reset phase `resetF`, the junction `junctionF`, the normal phase `normalF`, one revolution `revolutionF`, its iteration `revIter`, and the proofs (`…_spec`) that every successful computation is a genuine run of the machine |
| `Leading.lean` | the radix `rad2` of a counter position and its invariance under `addT` |
| `Shape.lean` | the radix pattern of the counter built by a reset phase (`resetF_pat`, `patF_true`) |
| `Success.lean` | `addT_of_le_gap`, `junctionF_isSome`, and `neverHalts_of_revIter`: if every revolution computes, the machine never halts |
| `CompletionArithmetic.lean` | the **exact** scalar reset maps `xnext`/`xfold`/`XSafe`, their inverses `inv`, the normal-phase word `fresh` and its requirement `need`, the junction word `suffix`, and the closure lemma `suffix_safe` |
| `CompletionSaturation.lean` | the saturation word `sat` of a counter, its invariance under increments (`sat_preserved`), and the exact descriptions `ovf_sat`, `normal_exact`, `junction_exact`, `revolution_suffix` |
| `Completion.lean` | the exact reset (`reset_exact`), inherited domination (`inherited_exact`), the invariant and its closure (`invariant_step`), the seed, and `neverHalts` |

`PROOF_OUTLINE.md` explains the mathematics.

## Finite certificates

Five statements are decided by compiled evaluation (`native_decide`); all of
them are finite and could equally be checked by any other evaluator (in Rocq:
`vm_compute`):

* `normal_small_certificate` — `need g + 30 ≤ 2 g` for the 67 values `133 ≤ g < 200`;
* `junction_small_certificate` — `suffixNeed g ≤ g` for the 273 even `62 ≤ g < 608`;
* `seed_reached`, `seed_safe`, `seed_gap` — the machine's second released block
  sequence is `seed`, it is safely resettable from gap 1, and its exact reset gap
  is `28958`.

Nothing else in the proof is a simulation: the infinite part is the induction of
`invariant_step` / `all_later_iterations`.

## Provenance

The machine semantics, the counter model, the executable revolution and the
reduction `neverHalts_of_revIter` were developed in earlier sessions of this
project.  The completing argument — exact reset maps, saturation invariance, the
explicit fresh word, and the even-gap-at-least-62 invariant — was supplied with
the task as an uncompiled candidate (`nonhalting_completion.zip`); it has been
repaired where it did not elaborate, checked, and it is what this project now
proves.
