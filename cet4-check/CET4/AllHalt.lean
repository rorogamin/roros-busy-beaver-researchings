/-
  CONJECTURE A: every machine in the ladder halts.

  STATUS: NOT PROVED. This file states the obligation and leaves it as `sorry`.
  `#print axioms all_halt` reports `sorryAx` — that is how you can tell at a
  glance that nothing has been established here.

  What a completed proof must supply: for each of the eleven pairs, an explicit
  `t` at which the heads collide. Two obstacles are worth naming up front.

    * For Comet the pipeline's claimed halt time is a power tower (~10↑↑24),
      which is not a `Nat`. A real proof needs either bignum arithmetic or a
      restatement as a growth relation on digit counts, not a value of `run`.

    * Nothing in the current evidence points the right way. All eleven pairs
      survive 4·10⁶ simulated steps without colliding (a screen, not proof:
      the BB(5) champion needs 47,176,870 steps, so a no-halt bound below that
      says nothing). No pair has a halt witness.
-/
import CET4.Ladder

open CET4

namespace CET4

/-- A halting pair halts within some bound. Genuinely proved. -/
theorem halts_implies_haltsBy (M : Pair) (h : Halts M) : ∃ N, HaltsBy M N := by
  rcases h with ⟨t, ht, heq⟩
  exact ⟨t, t, ht, Nat.le_refl t, heq⟩

/-- CONJECTURE A. Not proved: see the module comment. -/
theorem all_halt : AllHalt Ladder := by
  intro M hM
  sorry

#print axioms all_halt

end CET4
