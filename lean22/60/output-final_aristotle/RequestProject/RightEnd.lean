import RequestProject.Blocks

/-!
# The right-hand end of the tape

Combining the sweep theorems of `Blocks.lean` with the turn-around lemmas gives a
complete, unconditional description of what happens at the blank right end of the tape.
Over one full `6`-sweep cycle the bulk grows by exactly one `3`-cell block; the three
"bounce" theorems below are the three right-end turn-arounds of that cycle.

All three theorems put no constraint at all on the tape to the left of the bulk region,
so they can be combined with any analysis of the left-hand (irregular) end.
-/

namespace BB25

/-- `B` arriving at the right end `4 2 0 0` turns around into state `A`, leaving
`0 4 2 0`: a brand-new bulk block `042` has appeared. -/
theorem turn_B_four (T : ℤ → Sym) (p : ℤ) (h0 : T p = 4) (h1 : T (p + 1) = 2)
    (h2 : T (p + 2) = 0) (h3 : T (p + 3) = 0) :
    step^[7] ⟨St.B, p, T⟩ = ⟨St.A, p - 1, wr (wr (wr T p 0) (p + 1) 4) (p + 2) 2⟩ := by
  show step (step (step (step (step (step (step _)))))) = _
  rw [step_B4 T p h0]
  rw [step_B2 _ (p + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p + 1 + 1 = p + 2 by ring]
  rw [step_A0 _ (p + 2)
    (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2)]
  rw [show p + 2 + 1 = p + 3 by ring]
  rw [step_B0 _ (p + 3) (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
    exact h3)]
  rw [show p + 3 - 1 = p + 2 by ring]
  rw [step_A1 _ (p + 2) (by rw [wr_self])]
  rw [show p + 2 - 1 = p + 1 by ring]
  rw [step_A3 _ (p + 1)
    (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self])]
  rw [show p + 1 - 1 = p by ring]
  rw [step_B0 _ p (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), wr_self])]
  congr 1
  funext i
  by_cases e1 : i = p
  · simp [e1, wr, show p ≠ p + 1 by omega, show p ≠ p + 2 by omega]
  by_cases e2 : i = p + 1
  · simp [e2, wr, show p + 1 ≠ p + 2 by omega]
  by_cases e3 : i = p + 2
  · simp [e3, wr]
  · simp [wr, e1, e2, e3]

/-- Sweep 1 of the cycle, including the bounce at the blank right end: `A` crosses
`(042)^k`, writes a `2` in the first blank cell, and comes back to the right end of the
(now `(103)^k`) bulk, still in state `A`.  Cost: `3k + 3` steps. -/
theorem bounce_042 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 0 4 2 j)
    (hb0 : T (a + (3 * k : ℕ)) = 0) (hb1 : T (a + (3 * k : ℕ) + 1) = 0) :
    ∃ T' : ℤ → Sym, step^[3 * k + 3] ⟨St.A, a, T⟩ = ⟨St.A, a + (3 * k : ℕ) - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 1 0 3 j) ∧
      T' (a + (3 * k : ℕ)) = 2 ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) < i → T' i = T i) := by
  obtain ⟨T1, hs1, hin1, hout1⟩ := sweep_042 k T a h
  have e0 : T1 (a + (3 * k : ℕ)) = 0 := by rw [hout1 _ (Or.inr (by omega))]; exact hb0
  have e1 : T1 (a + (3 * k : ℕ) + 1) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb1
  have hs2 := turn_A_blank T1 (a + (3 * k : ℕ)) e0 e1
  refine ⟨wr T1 (a + (3 * k : ℕ)) 2, ?_, ?_, ?_, ?_⟩
  · rw [show 3 * k + 3 = 3 + 3 * k by ring, Function.iterate_add_apply, hs1, hs2]
  · intro j hj
    rw [wr_of_ne _ _ _ (by push_cast; omega)]
    exact hin1 j hj
  · exact wr_self _ _ _
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), hout1]
    rcases hi with hi | hi
    · left; exact hi
    · right; omega

/-- Sweep 3 of the cycle, including the bounce: `B` crosses `(204)^k` and turns around on
the `2` left by `bounce_042`, extending the right end to `4 2`.  Cost: `3k + 5` steps. -/
theorem bounce_204 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 2 0 4 j)
    (hb0 : T (a + (3 * k : ℕ)) = 2) (hb1 : T (a + (3 * k : ℕ) + 1) = 0)
    (hb2 : T (a + (3 * k : ℕ) + 2) = 0) :
    ∃ T' : ℤ → Sym, step^[3 * k + 5] ⟨St.B, a, T⟩ = ⟨St.B, a + (3 * k : ℕ) - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 3 1 0 j) ∧
      T' (a + (3 * k : ℕ)) = 4 ∧ T' (a + (3 * k : ℕ) + 1) = 2 ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) + 1 < i → T' i = T i) := by
  obtain ⟨T1, hs1, hin1, hout1⟩ := sweep_204 k T a h
  have e0 : T1 (a + (3 * k : ℕ)) = 2 := by rw [hout1 _ (Or.inr (by omega))]; exact hb0
  have e1 : T1 (a + (3 * k : ℕ) + 1) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb1
  have e2 : T1 (a + (3 * k : ℕ) + 2) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb2
  have hs2 := turn_B_two T1 (a + (3 * k : ℕ)) e0 e1 e2
  refine ⟨wr (wr T1 (a + (3 * k : ℕ)) 4) (a + (3 * k : ℕ) + 1) 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 3 * k + 5 = 5 + 3 * k by ring, Function.iterate_add_apply, hs1, hs2]
  · intro j hj
    rw [wr_of_ne _ _ _ (by push_cast; omega), wr_of_ne _ _ _ (by push_cast; omega)]
    exact hin1 j hj
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · exact wr_self _ _ _
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), hout1]
    rcases hi with hi | hi
    · left; exact hi
    · right; omega

/-- Sweep 5 of the cycle, including the bounce: `B` crosses `(420)^k` and turns around on
the `4 2` left by `bounce_204`, which becomes a fresh bulk block `042`.  This is the step
in which the bulk gains one block.  Cost: `3k + 7` steps. -/
theorem bounce_420 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 4 2 0 j)
    (hb0 : T (a + (3 * k : ℕ)) = 4) (hb1 : T (a + (3 * k : ℕ) + 1) = 2)
    (hb2 : T (a + (3 * k : ℕ) + 2) = 0) (hb3 : T (a + (3 * k : ℕ) + 3) = 0) :
    ∃ T' : ℤ → Sym, step^[3 * k + 7] ⟨St.B, a, T⟩ = ⟨St.A, a + (3 * k : ℕ) - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 0 3 1 j) ∧
      T' (a + (3 * k : ℕ)) = 0 ∧ T' (a + (3 * k : ℕ) + 1) = 4 ∧
      T' (a + (3 * k : ℕ) + 2) = 2 ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) + 2 < i → T' i = T i) := by
  obtain ⟨T1, hs1, hin1, hout1⟩ := sweep_420 k T a h
  have e0 : T1 (a + (3 * k : ℕ)) = 4 := by rw [hout1 _ (Or.inr (by omega))]; exact hb0
  have e1 : T1 (a + (3 * k : ℕ) + 1) = 2 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb1
  have e2 : T1 (a + (3 * k : ℕ) + 2) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb2
  have e3 : T1 (a + (3 * k : ℕ) + 3) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]; exact hb3
  have hs2 := turn_B_four T1 (a + (3 * k : ℕ)) e0 e1 e2 e3
  refine ⟨wr (wr (wr T1 (a + (3 * k : ℕ)) 0) (a + (3 * k : ℕ) + 1) 4)
    (a + (3 * k : ℕ) + 2) 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 3 * k + 7 = 7 + 3 * k by ring, Function.iterate_add_apply, hs1, hs2]
  · intro j hj
    rw [wr_of_ne _ _ _ (by push_cast; omega), wr_of_ne _ _ _ (by push_cast; omega),
      wr_of_ne _ _ _ (by push_cast; omega)]
    exact hin1 j hj
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · exact wr_self _ _ _
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      hout1]
    rcases hi with hi | hi
    · left; exact hi
    · right; omega

end BB25
