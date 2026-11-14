import RequestProject.Blocks

/-!
# Walls: the second kind of repeated region

Besides the `3`-periodic bulk analysed in `Blocks.lean`, the space-time diagram of
`1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` contains long runs of the single symbol `2`
("walls").  In the longitudinal picture a wall is a *plateau*: all its cells sit at the
same place of the period-`6` cycle, whereas in the bulk consecutive cells are offset by
two places.

A wall is not crossed in a single sweep.  Instead the head performs a ping-pong with
period `8`: a marker `0 3` travels through the wall, two cells at a time, leaving `1`s
behind (`wall_chain`).  What happens when the marker reaches the far end of the wall
depends on the parity of the length of the wall.  For an odd-length wall the head turns
around and the wall has grown by three cells (`wall_odd`); this is the mechanism by which
a wall eats the bulk.
-/

namespace BB25

/-! ### The basic `8`-step ping-pong -/

/-- The elementary wall step: the marker `0 3` moves two cells to the right through the
wall, leaving two `1`s behind.  Costs `8` steps. -/
lemma wall_step (T : ℤ → Sym) (p : ℤ) (h0 : T (p - 2) = 0) (h1 : T (p - 1) = 3)
    (h2 : T p = 2) (h3 : T (p + 1) = 2) :
    step^[8] ⟨St.A, p, T⟩ =
      ⟨St.A, p + 2, wr (wr (wr (wr T (p - 2) 1) (p - 1) 1) p 0) (p + 1) 3⟩ := by
  show step (step (step (step (step (step (step (step _))))))) = _
  rw [step_A2 T p h2]
  rw [step_B3 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p - 1 - 1 = p - 2 by ring]
  rw [step_A0 _ (p - 2)
    (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h0)]
  rw [show p - 2 + 1 = p - 1 by ring]
  rw [step_B4 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [show p - 1 + 1 = p by ring]
  rw [step_B3 _ p (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_self])]
  rw [show p - 1 = p - 1 by ring]
  rw [step_A0 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [show p - 1 + 1 = p by ring]
  rw [step_B4 _ p (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [step_B2 _ (p + 1) (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega)]
    exact h3)]
  congr 1
  · ring
  · funext i
    by_cases e1 : i = p - 2
    · simp [e1, wr, show p - 2 ≠ p - 1 by omega, show p - 2 ≠ p by omega,
        show p - 2 ≠ p + 1 by omega]
    by_cases e2 : i = p - 1
    · simp [e2, wr, show p - 1 ≠ p by omega, show p - 1 ≠ p + 1 by omega]
    by_cases e3 : i = p
    · simp [e3, wr, show p ≠ p + 1 by omega]
    by_cases e4 : i = p + 1
    · simp [e4, wr]
    · simp [wr, e1, e2, e3, e4]

/-- The marker `0 3` travels `2n` cells to the right through a wall of `2`s in `8n`
steps, turning the cells it passes into `1`s. -/
theorem wall_chain : ∀ (n : ℕ) (T : ℤ → Sym) (p : ℤ),
    T (p - 2) = 0 → T (p - 1) = 3 → (∀ j : ℕ, j < 2 * n → T (p + j) = 2) →
    ∃ T' : ℤ → Sym, step^[8 * n] ⟨St.A, p, T⟩ = ⟨St.A, p + (2 * n : ℕ), T'⟩ ∧
      (∀ i : ℤ, p - 2 ≤ i → i < p + (2 * n : ℕ) - 2 → T' i = 1) ∧
      T' (p + (2 * n : ℕ) - 2) = 0 ∧ T' (p + (2 * n : ℕ) - 1) = 3 ∧
      (∀ i : ℤ, i < p - 2 ∨ p + (2 * n : ℕ) ≤ i → T' i = T i) := by
  intro n
  induction n with
  | zero =>
      intro T p h0 h1 _
      refine ⟨T, by simp, ?_, ?_, ?_, ?_⟩
      · intro i hi hi'; push_cast at hi'; omega
      · simpa using h0
      · simpa using h1
      · intro i _; rfl
  | succ n ih =>
      intro T p h0 h1 hw
      have h2 : T p = 2 := by simpa using hw 0 (by omega)
      have h3 : T (p + 1) = 2 := by
        have := hw 1 (by omega); simpa using this
      set T1 := wr (wr (wr (wr T (p - 2) 1) (p - 1) 1) p 0) (p + 1) 3 with hT1
      have hs1 : step^[8] ⟨St.A, p, T⟩ = ⟨St.A, p + 2, T1⟩ := wall_step T p h0 h1 h2 h3
      have v1 : T1 (p - 2) = 1 := by
        rw [hT1, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
          wr_of_ne _ _ _ (by omega), wr_self]
      have v2 : T1 (p - 1) = 1 := by
        rw [hT1, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
      have v3 : T1 p = 0 := by rw [hT1, wr_of_ne _ _ _ (by omega), wr_self]
      have v4 : T1 (p + 1) = 3 := by rw [hT1, wr_self]
      have vout : ∀ i : ℤ, i < p - 2 ∨ p + 2 ≤ i → T1 i = T i := by
        intro i hi
        rw [hT1, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
          wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
      have hw' : ∀ j : ℕ, j < 2 * n → T1 (p + 2 + j) = 2 := by
        intro j hj
        rw [vout _ (Or.inr (by omega))]
        have := hw (j + 2) (by omega)
        rw [show p + ((j + 2 : ℕ) : ℤ) = p + 2 + j by push_cast; ring] at this
        exact this
      obtain ⟨T2, hs2, hones, hz, ht, hout⟩ := ih T1 (p + 2)
        (by rw [show p + 2 - 2 = p by ring]; exact v3)
        (by rw [show p + 2 - 1 = p + 1 by ring]; exact v4) hw'
      refine ⟨T2, ?_, ?_, ?_, ?_, ?_⟩
      · have e : 8 * (n + 1) = 8 * n + 8 := by ring
        rw [e, Function.iterate_add_apply, hs1, hs2]
        congr 1
        push_cast
        ring
      · intro i hi hi'
        rcases lt_or_ge i p with hlt | hge
        · -- i is `p-2` or `p-1`
          rw [hout _ (Or.inl (by omega))]
          have : i = p - 2 ∨ i = p - 1 := by omega
          rcases this with rfl | rfl
          · exact v1
          · exact v2
        · refine hones i (by omega) ?_
          push_cast at hi' ⊢
          omega
      · have := hz
        rw [show p + 2 + ((2 * n : ℕ) : ℤ) - 2 = p + ((2 * (n + 1) : ℕ) : ℤ) - 2 by
          push_cast; ring] at this
        exact this
      · have := ht
        rw [show p + 2 + ((2 * n : ℕ) : ℤ) - 1 = p + ((2 * (n + 1) : ℕ) : ℤ) - 1 by
          push_cast; ring] at this
        exact this
      · intro i hi
        have hi2 : i < p + 2 - 2 ∨ p + 2 + ((2 * n : ℕ) : ℤ) ≤ i := by
          rcases hi with hi | hi
          · left; omega
          · right; push_cast at hi ⊢; omega
        rw [hout _ hi2, vout]
        rcases hi with hi | hi
        · left; omega
        · right; push_cast at hi; omega

/-! ### The end of an odd wall -/

/-- When the marker reaches the last `2` of a wall (with a `0` just beyond it) the head
turns around: `10` steps later the three cells `0 3 2` have become `1 1 1` and the head
is back on the last of them, in state `A`. -/
lemma wall_odd_end (T : ℤ → Sym) (p : ℤ) (h0 : T (p - 2) = 0) (h1 : T (p - 1) = 3)
    (h2 : T p = 2) (h3 : T (p + 1) = 0) :
    step^[10] ⟨St.A, p, T⟩ = ⟨St.A, p, wr (wr (wr T (p - 2) 1) (p - 1) 1) p 1⟩ := by
  show step (step (step (step (step (step (step (step (step (step _))))))))) = _
  rw [step_A2 T p h2]
  rw [step_B3 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1)]
  rw [show p - 1 - 1 = p - 2 by ring]
  rw [step_A0 _ (p - 2)
    (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h0)]
  rw [show p - 2 + 1 = p - 1 by ring]
  rw [step_B4 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [show p - 1 + 1 = p by ring]
  rw [step_B3 _ p (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_self])]
  rw [step_A0 _ (p - 1) (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [show p - 1 + 1 = p by ring]
  rw [step_B4 _ p (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  rw [step_B0 _ (p + 1) (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega)]
    exact h3)]
  rw [show p + 1 - 1 = p by ring]
  rw [step_A0 _ p (by rw [wr_self])]
  rw [step_B0 _ (p + 1) (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
    exact h3)]
  rw [show p + 1 - 1 = p by ring]
  congr 1
  funext i
  by_cases e1 : i = p - 2
  · simp [e1, wr, show p - 2 ≠ p - 1 by omega, show p - 2 ≠ p by omega]
  by_cases e2 : i = p - 1
  · simp [e2, wr, show p - 1 ≠ p by omega]
  by_cases e3 : i = p
  · simp [e3, wr]
  · simp [wr, e1, e2, e3]

/-! ### Leftward run over a block of `1`s -/

/-- `A` moving leftwards over a run of `1`s turns them into `2`s, one cell per step. -/
theorem ones_left : ∀ (n : ℕ) (T : ℤ → Sym) (p : ℤ),
    (∀ j : ℕ, j ≤ n → T (p - j) = 1) →
    ∃ T' : ℤ → Sym, step^[n + 1] ⟨St.A, p, T⟩ = ⟨St.A, p - (n : ℕ) - 1, T'⟩ ∧
      (∀ j : ℕ, j ≤ n → T' (p - j) = 2) ∧
      (∀ i : ℤ, i < p - (n : ℕ) ∨ p < i → T' i = T i) := by
  intro n
  induction n with
  | zero =>
      intro T p h
      refine ⟨wr T p 2, ?_, ?_, ?_⟩
      · show step _ = _
        rw [step_A1 T p (by simpa using h 0 (le_refl 0))]
        congr 1
        push_cast
        ring
      · intro j hj
        interval_cases j
        simp
      · intro i hi
        exact wr_of_ne _ _ _ (by push_cast at hi; omega)
  | succ n ih =>
      intro T p h
      have hp : T p = 1 := by simpa using h 0 (by omega)
      have hs1 : step ⟨St.A, p, T⟩ = ⟨St.A, p - 1, wr T p 2⟩ := step_A1 T p hp
      have h' : ∀ j : ℕ, j ≤ n → (wr T p 2) (p - 1 - j) = 1 := by
        intro j hj
        rw [wr_of_ne _ _ _ (by omega)]
        have := h (j + 1) (by omega)
        rw [show p - ((j + 1 : ℕ) : ℤ) = p - 1 - j by push_cast; ring] at this
        exact this
      obtain ⟨T2, hs2, hin, hout⟩ := ih (wr T p 2) (p - 1) h'
      refine ⟨T2, ?_, ?_, ?_⟩
      · rw [show n + 1 + 1 = (n + 1) + 1 from rfl, Function.iterate_add_apply,
          Function.iterate_one, hs1, hs2]
        congr 1
        push_cast
        ring
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [hout _ (Or.inr (by push_cast; omega))]
          simp
        · have := hin (j - 1) (by omega)
          rw [show p - 1 - ((j - 1 : ℕ) : ℤ) = p - j by
            have : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
            rw [this]; ring] at this
          exact this
      · intro i hi
        have hi' : i < p - 1 - (n : ℕ) ∨ p - 1 < i := by
          rcases hi with hi | hi
          · left; push_cast at hi ⊢; omega
          · right; omega
        rw [hout _ hi', wr_of_ne _ _ _ ?_]
        rcases hi with hi | hi
        · push_cast at hi; omega
        · omega

/-! ### An odd wall grows by three cells

This is the complete description of the interaction of a rightward `A` sweep with a wall
of odd length: the head turns around, and the wall has swallowed one more bulk block. -/

/-- A wall of `2 n + 1` cells of `2`, preceded by a bulk block ending in `1 0 3` and
followed by a `0`, grows by three cells in `10 n + 14` steps, and the head comes back out
to the left in state `A`. -/
theorem wall_odd (n : ℕ) (T : ℤ → Sym) (p : ℤ)
    (hm : T (p - 3) = 1) (h0 : T (p - 2) = 0) (h1 : T (p - 1) = 3)
    (hwall : ∀ j : ℕ, j ≤ 2 * n → T (p + j) = 2)
    (hnext : T (p + (2 * n : ℕ) + 1) = 0) :
    ∃ T' : ℤ → Sym, step^[10 * n + 14] ⟨St.A, p, T⟩ = ⟨St.A, p - 4, T'⟩ ∧
      (∀ i : ℤ, p - 3 ≤ i → i ≤ p + (2 * n : ℕ) → T' i = 2) ∧
      (∀ i : ℤ, i < p - 3 ∨ p + (2 * n : ℕ) < i → T' i = T i) := by
  obtain ⟨T1, hs1, hones1, hz1, ht1, hout1⟩ :=
    wall_chain n T p h0 h1 (fun j hj => hwall j (by omega))
  set q : ℤ := p + ((2 * n : ℕ) : ℤ) with hq
  have e2 : T1 (q - 2) = 0 := hz1
  have e3 : T1 (q - 1) = 3 := ht1
  have e4 : T1 q = 2 := by
    rw [hout1 _ (Or.inr (by omega))]
    exact hwall (2 * n) (by omega)
  have e5 : T1 (q + 1) = 0 := by
    rw [hout1 _ (Or.inr (by omega))]
    exact hnext
  have hs2 : step^[10] ⟨St.A, q, T1⟩ =
      ⟨St.A, q, wr (wr (wr T1 (q - 2) 1) (q - 1) 1) q 1⟩ := wall_odd_end T1 q e2 e3 e4 e5
  set T2 := wr (wr (wr T1 (q - 2) 1) (q - 1) 1) q 1 with hT2
  have hT2ones : ∀ j : ℕ, j ≤ 2 * n + 3 → T2 (q - j) = 1 := by
    intro j hj
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · have : j = 0 := by omega
      subst this
      simp [hT2]
    rcases Nat.lt_or_ge j 2 with hj0 | hj2
    · have : j = 1 := by omega
      subst this
      rw [hT2, show q - ((1 : ℕ) : ℤ) = q - 1 by push_cast; ring,
        wr_of_ne _ _ _ (by omega), wr_self]
    rcases Nat.lt_or_ge j 3 with hj0 | hj3
    · have : j = 2 := by omega
      subst this
      rw [hT2, show q - ((2 : ℕ) : ℤ) = q - 2 by push_cast; ring,
        wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
    · have hlt : q - (j : ℤ) < q - 2 := by
        have : (3 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj3
        omega
      rw [hT2, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
        wr_of_ne _ _ _ (by omega)]
      rcases lt_or_ge (q - (j : ℤ)) (p - 2) with hcase | hcase
      · -- only `p - 3` is possible here
        have : q - (j : ℤ) = p - 3 := by
          have hjle : (j : ℤ) ≤ 2 * n + 3 := by exact_mod_cast hj
          rw [hq] at hcase ⊢
          push_cast at hcase hjle ⊢
          omega
        rw [this, hout1 _ (Or.inl (by omega))]
        exact hm
      · exact hones1 _ hcase (by omega)
  obtain ⟨T3, hs3, hin3, hout3⟩ := ones_left (2 * n + 3) T2 q hT2ones
  refine ⟨T3, ?_, ?_, ?_⟩
  · have hcomb : step^[10 + 8 * n] ⟨St.A, p, T⟩ = ⟨St.A, q, T2⟩ := by
      rw [Function.iterate_add_apply, hs1, hs2]
    have e : 10 * n + 14 = (2 * n + 3 + 1) + (10 + 8 * n) := by ring
    rw [e, Function.iterate_add_apply, hcomb, hs3]
    congr 1
    rw [hq]
    push_cast
    ring
  · intro i hi hi'
    have hqv : q = p + 2 * (n : ℤ) := by rw [hq]; push_cast; ring
    have hj : (q - i).toNat ≤ 2 * n + 3 := by omega
    have he : i = q - ((q - i).toNat : ℤ) := by omega
    rw [he]
    exact hin3 _ hj
  · intro i hi
    have hi3 : i < q - ((2 * n + 3 : ℕ) : ℤ) ∨ q < i := by
      rcases hi with hi | hi
      · left; rw [hq]; push_cast; omega
      · right; omega
    rw [hout3 _ hi3, hT2, wr_of_ne _ _ _ ?_, wr_of_ne _ _ _ ?_, wr_of_ne _ _ _ ?_,
      hout1 _ ?_]
    · rcases hi with hi | hi
      · left; omega
      · right; omega
    · rcases hi with hi | hi
      · omega
      · omega
    · rcases hi with hi | hi
      · omega
      · omega
    · rcases hi with hi | hi
      · omega
      · omega

end BB25
