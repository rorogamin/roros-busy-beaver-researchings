import RequestProject.MixedInv

/-!
# Non-halting of `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`

A finite bootstrap reaches the reset with body
`VVVVVVVVVVVVVVVV1VVVV1V1V10VVVV0101001010111111111` (reset 12), which satisfies
the closed invariant `Inv`; the invariant is preserved by every exact reset
return (`inv_step`), so the block system runs forever and the machine never
halts.
-/

namespace TM25

open LB RB Hd

/-- A reset step whose side conditions are checked by computation. -/
theorem boot_step (u : List RB) (N d : Nat)
    (h : cOK 0 u = true ∧ 7 ≤ cCap 0 u ∧ d < 2 ^ N ∧ cCap 0 u + 10 + d = 4 * 2 ^ N) :
    Reach (resetCfg (u ++ [C1])) (resetCfg (cEmit 0 u ++ compbits N d)) := by
  obtain ⟨t, -, ht⟩ := reset_return u h.1 h.2.1 N d h.2.2.1 h.2.2.2
  exact ⟨t, ht⟩

/-- Body of reset 8 without its final `C1`. -/
def u8 : List RB := [V, V, V, V, V, V, C1, C, C1]
def u9 : List RB := (cEmit 0 u8 ++ compbits 5 1).dropLast
def u10 : List RB := (cEmit 0 u9 ++ compbits 9 45).dropLast
def u11 : List RB := (cEmit 0 u10 ++ compbits 11 53).dropLast
/-- Body of reset 12, the seed of the invariant. -/
def w12 : List RB := cEmit 0 u11 ++ compbits 19 693

theorem w12_eq : w12 = [V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, C1, V, V, V, V, C1, V, C1,
    V, C1, C, V, V, V, V, C, C1, C, C1, C, C, C1, C, C1, C, C1, C1, C1, C1, C1, C1, C1, C1, C1] := by
  decide

set_option maxRecDepth 100000 in
/-- 504 block steps from `L W < C R` reach reset 8. -/
theorem arun_504 : arun 504 astart = some (resetCfg (u8 ++ [C1])) := by decide

theorem reach_w12 : Reach astart (resetCfg w12) := by
  refine (show Reach astart (resetCfg (u8 ++ [C1])) from ⟨504, arun_504⟩).trans ?_
  have e9 : cEmit 0 u8 ++ compbits 5 1 = u9 ++ [C1] := by decide
  have e10 : cEmit 0 u9 ++ compbits 9 45 = u10 ++ [C1] := by decide
  have e11 : cEmit 0 u10 ++ compbits 11 53 = u11 ++ [C1] := by decide
  refine (boot_step u8 5 1 (by decide)).trans ?_
  rw [e9]
  refine (boot_step u9 9 45 (by decide)).trans ?_
  rw [e10]
  refine (boot_step u10 11 53 (by decide)).trans ?_
  rw [e11]
  exact boot_step u11 19 693 (by decide)

/-- The seed satisfies the invariant (all four clauses are finite computations;
its debt is `1106942` at height `36`). -/
theorem inv_w12 : Inv w12 :=
  ⟨by unfold Letters; decide, ⟨w12.take 44, by decide⟩, by decide, ⟨36, by decide, by decide⟩⟩

/-- Every reachable invariant reset has reachable invariant resets arbitrarily
far in the future. -/
theorem reach_far : ∀ k, ∃ t, k ≤ t ∧ ∃ w, Inv w ∧ arun t astart = some (resetCfg w) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := reach_w12
    exact ⟨t, Nat.zero_le _, w12, inv_w12, ht⟩
  | succ k ih =>
    obtain ⟨t, hk, w, hw, ht⟩ := ih
    obtain ⟨w', hw', s, hs, hrun⟩ := inv_step w hw
    exact ⟨t + s, by omega, w', hw', arun_comp ht hrun⟩

/-- **The block system started at `L W < C R` never halts.** -/
theorem astart_never_halts : ANeverHalts astart := by
  intro n a ha hh
  obtain ⟨t, ht, w, -, hrun⟩ := reach_far (n + 1)
  have h1 : (arun (n + 1) astart).isSome := arun_isSome_of_le ht (by rw [hrun]; simp)
  rw [arun_add, ha] at h1
  simp [arun, hh] at h1

/-- **The Turing machine `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---` does not halt
when started on the blank tape.** -/
theorem machine_never_halts : ¬ Halts := not_halts_of_never astart_never_halts

end TM25
