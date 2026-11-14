/-
  Machine 14: assembly layer for a block invariant.

  This file connects the completed raw bridge (`Machine14Bridge.lean`) to the
  shape a nonhalting proof must have.  It does **not** prove that machine 14 is
  nonhalting: the premise `TotalOn P` is exactly the missing strengthened
  invariant.  The last theorem shows that producing such a `P` is equivalent
  to proving the block run total, so this file isolates the obligation rather
  than disguising it as a completed proof.
-/

import Machine14Bridge

namespace M14

/-- A block predicate strong enough to make the block simulation total.  The
second component is the induction step: every `P`-state has a defined block
successor which is again a `P`-state. -/
def TotalOn (P : BState → Prop) : Prop :=
  P initB ∧ ∀ s, P s → ∃ s', stepB s = some s' ∧ P s'

/-- `TotalOn P` gives a total block run, with `P` holding at every stage. -/
theorem runB_total_and_inv_of_totalOn {P : BState → Prop} (h : TotalOn P) :
    ∀ n, ∃ s, runB n = some s ∧ P s := by
  intro n
  induction n with
  | zero =>
      exact ⟨initB, rfl, h.1⟩
  | succ n ih =>
      rcases ih with ⟨s, hs, hP⟩
      rcases h.2 s hP with ⟨s', hstep, hP'⟩
      exact ⟨s', by simp [runB, ostepB, hs, hstep], hP'⟩

/-- Consequently the block run never reaches `none`. -/
theorem runB_total_of_totalOn {P : BState → Prop} (h : TotalOn P) :
    ∀ n, ∃ s, runB n = some s := by
  intro n
  rcases runB_total_and_inv_of_totalOn h n with ⟨s, hs, _⟩
  exact ⟨s, hs⟩

/-- Every stage of that total block run is realized by the actual raw machine,
using the completed raw-to-block bridge.  This is a statement about block
stages, not about every intermediate raw time. -/
theorem raw_stage_bridge_of_totalOn {P : BState → Prop} (h : TotalOn P) :
    ∀ n, ∃ s k, runB n = some s ∧ rawRun (14 + k) = some (rawOf s) := by
  intro n
  rcases runB_total_of_totalOn h n with ⟨s, hs⟩
  rcases rawRun_bridges_runB hs with ⟨k, hk⟩
  exact ⟨s, k, hs, hk⟩

/-- Packaging the missing invariant as `TotalOn P` loses nothing: such a
predicate exists exactly when the block run is total.  Thus the remaining
work is genuinely the block-totality obligation, not a separate bookkeeping
problem. -/
theorem exists_totalOn_iff_block_total :
    (∃ P : BState → Prop, TotalOn P) ↔ ∀ n, ∃ s, runB n = some s := by
  constructor
  · rintro ⟨P, hP⟩
    exact runB_total_of_totalOn hP
  · intro htotal
    refine ⟨fun s => ∃ n, runB n = some s, ?_⟩
    constructor
    · exact ⟨0, rfl⟩
    · rintro s ⟨n, hs⟩
      rcases htotal (n + 1) with ⟨s', hs'⟩
      have hstep : stepB s = some s' := by
        simpa [runB, ostepB, hs] using hs'
      exact ⟨s', hstep, ⟨n + 1, hs'⟩⟩

#print axioms M14.runB_total_and_inv_of_totalOn
#print axioms M14.runB_total_of_totalOn
#print axioms M14.raw_stage_bridge_of_totalOn
#print axioms M14.exists_totalOn_iff_block_total

end M14
