# Non-halting of `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`

Main theorem: `TM25.machine_never_halts : ¬ TM25.Halts` in
`RequestProject/NonHalting.lean`.

* It is checked by Lean 4.28.0 with **no Mathlib and no other dependency**:
  only core Lean (`Nat`, `Int`, `List`, `Option`).
* Axioms: `propext`, `Classical.choice`, `Quot.sound`. It uses no `sorry`,
  no `native_decide` and no added axioms.
* Size: 7 files, about 1400 lines. A clean build takes a few seconds.

The argument follows the proof in the `bb25_mixed_counter_nonhalting_proof`
package that was supplied, with the simplifications listed at the end.

## File map (in dependency order)

| File | Contents |
|---|---|
| `TM.lean` | The machine: `trans`, `step`, `run`, `init`, and `Halts := ∃ n, run n init = none`. |
| `Blocks.lean` | Blocks `W U D` / `V C C1 G P S Q`, heads `< > w> lB`, the block step `astep`, and the fact that every block step is a real machine run (`astep_next`, each rule proved by `rfl` for an arbitrary tape context). Also the left-end loop, `arun`, `astart = L W < C R` (`start_21`), and `not_halts_of_never`. |
| `MixedLeft.lean` | `Reach`, the capacity `Kcap` of a mixed left word and its saturation image `Phi`. `left_excursion` (the mixed-left lemma) and `cascade` (the wide cascade, via the validity/capacity/image functions `cOK`, `cCap`, `cEmit`). |
| `MixedReset.lean` | The right counter `encR` (one integer `M`), `right_exc` (a right excursion is `M ↦ M+1`), `pair_iter`, `cgg_phase`, `compbits`, `encR_comp`, and **`reset_return`** (the exact reset-to-reset map). |
| `MixedArith.lean` | The debt scan `hs`/`xs`/`pc`/`em`. `mu_mono` (normalized debt is nondecreasing), `cascade_of_debt` (safe-cascade lemma), `image_bound` (the emitted prefix attenuates inherited debt), `cost_bound` (a complemented suffix costs `≤ 8d+2`), and lemmas about digits. |
| `MixedInv.lean` | The invariant `Inv` and **`inv_step`**: `Inv w → ∃ w', Inv w' ∧ reset(w) →⁺ reset(w')`. |
| `NonHalting.lean` | Bootstrap: 504 block steps reach reset 8 (`arun_504`), then four `reset_return`s reach the 50-letter seed `w12`, and `inv_w12`. From these, `reach_far`, `astart_never_halts` and `machine_never_halts`. |

## The proof in brief

1. **Block reduction** (`Blocks.lean`). The machine halts only if the block system started at
   `L W < C R` reaches the pattern `D lB`. Every block step is an honest run of the machine,
   and `L lB` loops forever.
2. **Mixed left counter** (`MixedLeft.lean`). Define
   `K [] = 0`, `K (U l) = 2K l + 1`, `K (W l) = 2K l`, `K (D l) = ⌊K l / 2⌋`.
   A left excursion `⟨l, <, rs⟩ →* ⟨l', >, rs⟩` exists iff `K l > 0`. It gives
   `K l' = K l − 1` and leaves the image `Phi` unchanged. When `K l = 0` the excursion
   reaches the left end and writes `Phi l` in front of `rs`.
3. **Wide cascade** (`MixedLeft.lean`). Reading `V`/`C1`/`C` with left capacity `E` needs
   `E ≥ 0/1/6` and gives `2E+1`/`2E−1`/`⌊(E−6)/2⌋`.
4. **Right counter** (`MixedReset.lean`). `encR M` lists the bits of `M` below its two
   leading bits, followed by `P Q` if the second leading bit is 1. A right excursion maps
   `encR M` to `encR (M+1)` without touching the left word.
5. **Exact reset return** (`reset_return`). If the cascade through `u` is valid,
   `cCap 0 u ≥ 7`, `cCap 0 u + 10 + d = 4·2^N` and `d < 2^N`, then
   `L < u C1 P Q →⁺ L < cEmit 0 u ++ compbits N d P Q`.
6. **Arithmetic** (`MixedArith.lean`, `MixedInv.lean`). The capacity is `E = 2^h − 1 − x`.
   The invariant is: letters in `{V, C, C1}`, at least six trailing `C1`s, at least three
   promotions, and `256·x ≤ 2^h`. It is preserved by the return map.
7. **Seed** (`NonHalting.lean`). Reset 12 satisfies the invariant (finite computation by
   `decide`), and so every later reset does too. The run is therefore unbounded.

## Notes for a Rocq translation

* The work splits cleanly into three parts:
  * the concrete machine and block simulation (`TM`, `Blocks`), where every rule is
    closed by computation;
  * the operational lemmas (`MixedLeft`, `MixedReset`), which are structural inductions
    over the rules;
  * pure `Nat`/`Int` arithmetic (`MixedArith`, `MixedInv`).
* Rationals are not used. Every normalized-debt comparison `x/2^a ≤ x'/2^b` is stated with
  the denominators cleared, as `x · 2^b ≤ x' · 2^a`. The only integer-valued function is
  the height change `hs`.
* The tactics used are `omega` (→ `lia`), `simp`/`decide`/`rfl` (→ `simpl`/`vm_compute`/
  `reflexivity`) and `grind`. `grind` is used for a handful of nonlinear `Nat` identities
  and inequalities (→ `nia`/`ring`).
* The only non-trivial computations are:
  * `arun 504 astart` (504 block steps);
  * the four bootstrap returns and the invariant check on the 50-letter seed (numbers
    below `2^40`).
* Well-founded recursion appears only in `encR`, via `M / 2`. The bootstrap never
  evaluates it; it goes through `encR_comp` instead.

## Checking the supplied proof: findings

The supplied mathematical argument is correct. Everything it needs has been formalized.
While formalizing it, these simplifications turned up:

* The count clause `#V − #0 − #1 = 2` of invariant (14) is **not needed**. The debt bound
  together with six trailing ones already forces `H ≥ 15`, so the clause was dropped.
* The contraction by 3/8 is stronger than necessary. Only preservation of
  `μ ≤ 1/256` is used. It follows from the cruder bound `y + 8d + 2 ≤ (z+1)·4^p`.
* "Interpreting `G` as the digit −1" (§4.2) is not used. The six right excursions from
  `C G G` are carried out explicitly, as §4.2 also says.
* The Python/C checks and the block-step counts of later resets in the package are not
  needed. Only reset 8 (504 block steps) and the four returns to reset 12 are computed.

Earlier exploratory material (partial safety theorems, simulators, the 10⁸-step
check) was removed from this tree because the proof does not depend on it. It is
still available in the git history.
