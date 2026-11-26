/-
  CONJECTURE B: no machine in the ladder halts.

  STATUS: NOT PROVED. This file states the obligation and leaves it as `sorry`.
  `#print axioms none_halt` reports `sorryAx`.

  What a completed proof must supply: for each of the eleven pairs, an inductive
  invariant showing the heads never occupy the same cell. For the pairs examined
  so far both components look finite-state — one agent confined to a box roughly
  `L2` cells wide, the other executing a repeating cycle with net drift — so a
  periodic-orbit certificate may be reachable for some of them. None has been
  constructed.

  Note that this conjecture is strictly stronger than any simulation result:
  surviving 4·10⁶ steps is consistent with halting at 10↑↑24, and a proof of
  non-halting must exclude every finite time.
-/
import CET4.Ladder

open CET4

namespace CET4

/-- Non-halting rules out every finite halting bound. Genuinely proved. -/
theorem noneHalt_no_haltsBy (L : List Pair) (h : NoneHalt L) (N : Nat) :
    ∀ M, M ∈ L → ¬ HaltsBy M N := by
  intro M hM
  rintro ⟨t, ht1, _htN, heq⟩
  exact h M hM t ht1 heq

/-- CONJECTURE B. Not proved: see the module comment. -/
theorem none_halt : NoneHalt Ladder := by
  intro M hM
  sorry

#print axioms none_halt

end CET4
