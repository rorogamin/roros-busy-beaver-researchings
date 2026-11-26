/-
  CONJECTURE C: the ladder is mixed — at least one machine halts and at least one
  does not.

  STATUS: NOT PROVED. Both conjuncts are open obligations.

  This is the most plausible of the three conjectures and the hardest to settle.
  Proving it requires one of each kind of evidence:

    * a halt witness for some machine — an explicit `t` with colliding heads,
      which is a finite, checkable object; and
    * a non-halting invariant for some other machine — forever outside the reach
      of any simulation.

  In the other direction it is the *least* falsifiable: `AllHalt` dies to a single
  non-halting proof, `NoneHalt` dies to a single halt witness, but `Mixed` only
  dies when all eleven are settled one way. That makes it a poor subject for a
  falsification contest and a fair statement of the current best guess.

  What the evidence actually says: all eleven pairs behave qualitatively the same
  way over 4·10⁶ steps — one agent confined to a box roughly `L2` wide, one agent
  in a repeating cycle with net drift, no collisions. Uniformity weakly favours
  Conjecture B, but a screen of that length carries no tetrational weight.
-/
import CET4.Ladder

open CET4

namespace CET4

/-- CONJECTURE C. Not proved: see the module comment. -/
theorem mixed_ladder : Mixed Ladder := by
  sorry

#print axioms mixed_ladder

end CET4
