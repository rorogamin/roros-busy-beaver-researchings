import RequestProject.ResetPhase

/-!
# Chains of macro steps

`MPlus a b` says that the macro machine goes from `a` to `b` in at least one
step; `MPlus.sim` turns it into a positive-length run of the Turing machine and
`plus_chain_reaches` turns an infinite chain of such steps into an infinite run:
for every `k` there is an `n ≥ k` with `run (enc (f 0)) n = some (enc (f k))`.
This is what makes an infinite sequence of revolutions imply non-halting
(`neverHalts_of_revIter`).
-/

namespace SOC

open Cfg

/-! ## No `3` is ever released -/

/-! ## Macro steps, at least one of them -/

/-- `MPlus a b` : `b` is reached from `a` in at least one macro step. -/
def MPlus (a b : MCfg) : Prop := ∃ c, MStep a c ∧ MSteps c b

theorem reaches1_trans_reaches {c d e : Cfg} (h₁ : c ⟶+ d) (h₂ : d ⟶* e) : c ⟶+ e := by
  obtain ⟨m, hm, hm'⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by omega, run_trans hm' hn⟩

/-- A chain of at least one macro step is a run of at least one machine step. -/
theorem MPlus.sim {a b : MCfg} (h : MPlus a b) : enc a ⟶+ enc b := by
  obtain ⟨c, hc, hcb⟩ := h
  exact reaches1_trans_reaches (mstep_sim hc) hcb.sim

theorem plus_chain_reaches (f : Nat → MCfg) (hf : ∀ i, MPlus (f i) (f (i + 1))) :
    ∀ k, ∃ n, k ≤ n ∧ run (enc (f 0)) n = some (enc (f k)) := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
      obtain ⟨n, hn, hrun⟩ := ih
      obtain ⟨p, hp, hrp⟩ := (hf k).sim
      exact ⟨n + p, by omega, run_trans hrun hrp⟩

end SOC
