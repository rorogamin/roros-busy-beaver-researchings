import RequestProject.Sweeps

/-!
# The six block rules and the right-end turn-arounds

This file discharges the six `BlockR`/`BlockL` hypotheses and packages them into the six
sweep theorems `sweep_042`, …, `sweep_031`, valid for an arbitrary number `k` of blocks.

It also proves the three "turn-around" lemmas that describe what the machine does when a
sweep arrives at the blank right-hand end of the tape.
-/

namespace BB25

/-! ### The six block rules -/

lemma blockR_042 : BlockR St.A 0 4 2 1 0 3 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr (wr T a 1) (a + 1) 0) (a + 2) 3, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_A0 T a h0]
    rw [step_B4 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
    rw [show a + 1 + 1 = a + 2 by ring]
    rw [step_B2 _ (a + 2)
      (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2)]
    congr 1
    ring
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_self]
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

lemma blockL_103 : BlockL St.A 1 0 3 2 0 4 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr T (a + 2) 4) a 2, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_A3 T (a + 2) h2]
    rw [show a + 2 - 1 = a + 1 by ring]
    rw [step_B0 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
    rw [show a + 1 - 1 = a by ring]
    rw [step_A1 _ a (by rw [wr_of_ne _ _ _ (by omega)]; exact h0)]
  · rw [wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h1
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

lemma blockR_204 : BlockR St.B 2 0 4 3 1 0 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr (wr T a 3) (a + 1) 1) (a + 2) 0, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_B2 T a h0]
    rw [step_A0 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
    rw [show a + 1 + 1 = a + 2 by ring]
    rw [step_B4 _ (a + 2)
      (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2)]
    congr 1
    ring
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_self]
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

lemma blockL_310 : BlockL St.B 3 1 0 4 2 0 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr T (a + 1) 2) a 4, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_B0 T (a + 2) h2]
    rw [show a + 2 - 1 = a + 1 by ring]
    rw [step_A1 _ (a + 1) h1]
    rw [show a + 1 - 1 = a by ring]
    rw [step_A3 _ a (by rw [wr_of_ne _ _ _ (by omega)]; exact h0)]
  · rw [wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

lemma blockR_420 : BlockR St.B 4 2 0 0 3 1 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr (wr T a 0) (a + 1) 3) (a + 2) 1, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_B4 T a h0]
    rw [step_B2 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
    rw [show a + 1 + 1 = a + 2 by ring]
    rw [step_A0 _ (a + 2)
      (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2)]
    congr 1
    ring
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · rw [wr_self]
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

lemma blockL_031 : BlockL St.A 0 3 1 0 4 2 := by
  intro T a h0 h1 h2
  refine ⟨wr (wr T (a + 2) 2) (a + 1) 4, ?_, ?_, ?_, ?_, ?_⟩
  · show step (step (step _)) = _
    rw [step_A1 T (a + 2) h2]
    rw [show a + 2 - 1 = a + 1 by ring]
    rw [step_A3 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
    rw [show a + 1 - 1 = a by ring]
    rw [step_B0 _ a (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h0)]
  · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h0
  · rw [wr_self]
  · rw [wr_of_ne _ _ _ (by omega), wr_self]
  · intro i hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

/-! ### The six sweep theorems

Each of these says: a bulk region consisting of `k` copies of a `3`-cell block is crossed
in exactly `3 * k` steps, the state is unchanged, the head ends up just outside the
region, and every block has been advanced by one place in the `6`-cycle. -/

/-- `A` sweeps rightwards across `(042)^k`, leaving `(103)^k`. -/
theorem sweep_042 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 0 4 2 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.A, a, T⟩ = ⟨St.A, a + (3 * k : ℕ), T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 1 0 3 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainR blockR_042 k T a h

/-- `A` sweeps leftwards across `(103)^k`, leaving `(204)^k`. -/
theorem sweep_103 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 1 0 3 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.A, a + (3 * k : ℕ) - 1, T⟩ = ⟨St.A, a - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 2 0 4 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainL blockL_103 k T a h

/-- `B` sweeps rightwards across `(204)^k`, leaving `(310)^k`. -/
theorem sweep_204 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 2 0 4 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.B, a, T⟩ = ⟨St.B, a + (3 * k : ℕ), T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 3 1 0 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainR blockR_204 k T a h

/-- `B` sweeps leftwards across `(310)^k`, leaving `(420)^k`. -/
theorem sweep_310 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 3 1 0 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.B, a + (3 * k : ℕ) - 1, T⟩ = ⟨St.B, a - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 4 2 0 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainL blockL_310 k T a h

/-- `B` sweeps rightwards across `(420)^k`, leaving `(031)^k`. -/
theorem sweep_420 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 4 2 0 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.B, a, T⟩ = ⟨St.B, a + (3 * k : ℕ), T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 0 3 1 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainR blockR_420 k T a h

/-- `A` sweeps leftwards across `(031)^k`, leaving `(042)^k`: the cycle closes. -/
theorem sweep_031 (k : ℕ) (T : ℤ → Sym) (a : ℤ)
    (h : ∀ j : ℕ, j < 3 * k → T (a + j) = pat 0 3 1 j) :
    ∃ T' : ℤ → Sym, step^[3 * k] ⟨St.A, a + (3 * k : ℕ) - 1, T⟩ = ⟨St.A, a - 1, T'⟩ ∧
      (∀ j : ℕ, j < 3 * k → T' (a + j) = pat 0 4 2 j) ∧
      (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) :=
  chainL blockL_031 k T a h

/-! ### Turn-arounds at the blank right end -/

/-- `A` arriving at the blank right end: it writes a single `2` and turns around,
still in state `A`.  This is the step that makes the tape grow on the right. -/
theorem turn_A_blank (T : ℤ → Sym) (p : ℤ) (h0 : T p = 0) (h1 : T (p + 1) = 0) :
    step^[3] ⟨St.A, p, T⟩ = ⟨St.A, p - 1, wr T p 2⟩ := by
  show step (step (step _)) = _
  rw [step_A0 T p h0]
  rw [step_B0 _ (p + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p + 1 - 1 = p by ring]
  rw [step_A1 _ p (by rw [wr_self])]
  congr 1
  funext i
  by_cases h : i = p <;> simp [wr, h]

/-- `B` arriving at the `2` left behind by `turn_A_blank`: it turns around in state `B`,
converting the right end into `… 4 2 0 0 …`. -/
theorem turn_B_two (T : ℤ → Sym) (p : ℤ) (h0 : T p = 2) (h1 : T (p + 1) = 0)
    (h2 : T (p + 2) = 0) :
    step^[5] ⟨St.B, p, T⟩ = ⟨St.B, p - 1, wr (wr T p 4) (p + 1) 2⟩ := by
  show step (step (step (step (step _)))) = _
  rw [step_B2 T p h0]
  rw [step_A0 _ (p + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p + 1 + 1 = p + 2 by ring]
  rw [step_B0 _ (p + 2)
    (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2)]
  rw [show p + 2 - 1 = p + 1 by ring]
  rw [step_A1 _ (p + 1) (by rw [wr_self])]
  rw [show p + 1 - 1 = p by ring]
  rw [step_A3 _ p (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self])]
  congr 1
  funext i
  by_cases hp : i = p
  · subst hp; simp [wr, show i ≠ i + 1 by omega]
  · by_cases hq : i = p + 1 <;> simp [wr, hp, hq]

/-- `B` arriving at the blank right end simply turns around into state `A`,
writing nothing. -/
theorem turn_B_blank (T : ℤ → Sym) (p : ℤ) (h0 : T p = 0) :
    step ⟨St.B, p, T⟩ = ⟨St.A, p - 1, T⟩ :=
  step_B0 T p h0

end BB25
