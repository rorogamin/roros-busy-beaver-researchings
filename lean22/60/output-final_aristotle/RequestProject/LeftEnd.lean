import RequestProject.Machine

/-!
# The blank left end

The irregular region of the space-time diagram sits at the left end of the tape, and a
closed description of it is what is still missing for a proof of non-halting.  This file
records the one completely general rule there: what the machine does when it steps onto
fresh blank cells on the left while in state `A`.
-/

namespace BB25

/-- `A` standing on a blank cell with a blank cell on either side writes `1 3` to the
left of itself and steps one cell to the right, still in state `A` and still reading the
same symbol.  This is the rule by which the tape grows on the left; it is applied once
every time the head reaches a new leftmost position. -/
theorem left_blank_extend (T : ℤ → Sym) (p : ℤ) (hm : T (p - 1) = 0) (h0 : T p = 0)
    (h1 : T (p + 1) = 0) :
    step^[5] ⟨St.A, p, T⟩ = ⟨St.A, p + 1, wr (wr T (p - 1) 1) p 3⟩ := by
  show step (step (step (step (step _)))) = _
  rw [step_A0 T p h0]
  rw [step_B0 _ (p + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p + 1 - 1 = p by ring]
  rw [step_A1 _ p (by rw [wr_self])]
  rw [step_A0 _ (p - 1) (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
    exact hm)]
  rw [show p - 1 + 1 = p by ring]
  rw [step_B2 _ p (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  congr 1
  funext i
  by_cases e1 : i = p - 1
  · simp [e1, wr, show p - 1 ≠ p by omega]
  by_cases e2 : i = p
  · simp [e2, wr]
  · simp [wr, e1, e2]

end BB25
