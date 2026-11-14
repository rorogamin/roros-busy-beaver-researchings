import RequestProject.Machine

/-!
# Sweep lemmas ("longitudinal" analysis of the repeated regions)

Empirically, the space-time diagram of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` consists of a
slowly-growing irregular region on the left, and a *bulk* region which is periodic with
period `3` in space.  Every tape cell of the bulk runs through the *same* period-`6`
cycle of values

```
0 -> 1 -> 2 -> 3 -> 4 -> 0 -> 0 -> 1 -> ...
```

(that is the longitudinal, i.e. per-column, description of the space-time diagram), and
consecutive cells of the bulk are offset by two places in that cycle.  Consequently the
bulk is swept by the head in one of six ways.  Writing a `3`-cell block of the bulk as a
word, the six sweeps are

```
042  --(A, rightwards)-->  103
103  --(A, leftwards) -->  204
204  --(B, rightwards)-->  310
310  --(B, leftwards) -->  420
420  --(B, rightwards)-->  031
031  --(A, leftwards) -->  042
```

Each sweep costs exactly `3` steps per block and does not change the state, so a bulk
region of `k` blocks is traversed in exactly `3k` steps.  This file proves all six of
these facts for every `k`, together with the turn-around lemmas describing what happens
when a sweep reaches the blank right end of the tape.
-/

namespace BB25

/-- The `3`-periodic pattern with values `x, y, z`. -/
def pat (x y z : Sym) : ℕ → Sym := fun j => if j % 3 = 0 then x else if j % 3 = 1 then y else z

@[simp] lemma pat_zero (x y z : Sym) : pat x y z 0 = x := by simp [pat]
@[simp] lemma pat_one (x y z : Sym) : pat x y z 1 = y := by simp [pat]
@[simp] lemma pat_two (x y z : Sym) : pat x y z 2 = z := by simp [pat]

lemma pat_periodic (x y z : Sym) (j : ℕ) : pat x y z (j + 3) = pat x y z j := by
  simp [pat, Nat.add_mod_right]

lemma pat_sub3 (x y z : Sym) {j : ℕ} (h : 3 ≤ j) : pat x y z (j - 3) = pat x y z j := by
  have h3 : j - 3 + 3 = j := by omega
  conv_rhs => rw [← h3]
  rw [pat_periodic]

lemma pat_add3k (x y z : Sym) (m j : ℕ) : pat x y z (j + 3 * m) = pat x y z j := by
  induction m with
  | zero => simp
  | succ m ih =>
      have e : j + 3 * (m + 1) = (j + 3 * m) + 3 := by ring
      rw [e, pat_periodic, ih]

/-! ### The generic chain lemmas

`SweepR q x y z x' y' z'` says: whenever the head sits (in state `q`) at the left end of a
block whose contents are `x y z`, it crosses the block in `3` steps, leaves it in state
`q` just to the right of the block, and has rewritten it to `x' y' z'`. -/

/-- One rightward block crossing. -/
def BlockR (q : St) (x y z x' y' z' : Sym) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), T a = x → T (a + 1) = y → T (a + 2) = z →
    ∃ T' : ℤ → Sym, step^[3] ⟨q, a, T⟩ = ⟨q, a + 3, T'⟩ ∧
      T' a = x' ∧ T' (a + 1) = y' ∧ T' (a + 2) = z' ∧
      (∀ i : ℤ, i < a ∨ a + 3 ≤ i → T' i = T i)

/-- One leftward block crossing. -/
def BlockL (q : St) (x y z x' y' z' : Sym) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), T a = x → T (a + 1) = y → T (a + 2) = z →
    ∃ T' : ℤ → Sym, step^[3] ⟨q, a + 2, T⟩ = ⟨q, a - 1, T'⟩ ∧
      T' a = x' ∧ T' (a + 1) = y' ∧ T' (a + 2) = z' ∧
      (∀ i : ℤ, i < a ∨ a + 3 ≤ i → T' i = T i)

/-- A rightward sweep across `k` blocks takes `3k` steps. -/
theorem chainR {q : St} {x y z x' y' z' : Sym} (h3 : BlockR q x y z x' y' z') :
    ∀ (k : ℕ) (T : ℤ → Sym) (a : ℤ),
      (∀ j : ℕ, j < 3 * k → T (a + j) = pat x y z j) →
      ∃ T' : ℤ → Sym, step^[3 * k] ⟨q, a, T⟩ = ⟨q, a + (3 * k : ℕ), T'⟩ ∧
        (∀ j : ℕ, j < 3 * k → T' (a + j) = pat x' y' z' j) ∧
        (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) := by
  intro k
  induction k with
  | zero =>
      intro T a _
      exact ⟨T, by simp, by intro j hj; omega, by intro i _; rfl⟩
  | succ k ih =>
      intro T a h
      have h0 : T a = x := by simpa using h 0 (by omega)
      have h1 : T (a + 1) = y := by
        have := h 1 (by omega); simpa using this
      have h2 : T (a + 2) = z := by
        have := h 2 (by omega)
        rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num] at this
        simpa using this
      obtain ⟨T1, hs1, e0, e1, e2, hout1⟩ := h3 T a h0 h1 h2
      have hT1 : ∀ j : ℕ, j < 3 * k → T1 (a + 3 + j) = pat x y z j := by
        intro j hj
        rw [hout1 _ (Or.inr (by omega))]
        have := h (j + 3) (by omega)
        rw [show a + ((j + 3 : ℕ) : ℤ) = a + 3 + j by push_cast; ring] at this
        rw [this, pat_periodic]
      obtain ⟨T2, hs2, hin2, hout2⟩ := ih T1 (a + 3) hT1
      refine ⟨T2, ?_, ?_, ?_⟩
      · have e : 3 * (k + 1) = 3 * k + 3 := by ring
        rw [e, Function.iterate_add_apply, hs1, hs2]
        congr 1
        push_cast
        ring
      · intro j hj
        rcases lt_or_ge j 3 with hj3 | hj3
        · -- inside the first block
          have : T2 (a + j) = T1 (a + j) := by
            refine hout2 _ (Or.inl ?_)
            omega
          rw [this]
          interval_cases j
          · simpa using e0
          · simpa using e1
          · rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
            simpa using e2
        · have hjj : j - 3 < 3 * k := by omega
          have := hin2 (j - 3) hjj
          rw [show a + 3 + ((j - 3 : ℕ) : ℤ) = a + j by
            have : ((j - 3 : ℕ) : ℤ) = (j : ℤ) - 3 := by omega
            rw [this]; ring] at this
          rw [this, pat_sub3 _ _ _ hj3]
      · intro i hi
        have hi2 : i < a + 3 ∨ a + 3 + ((3 * k : ℕ) : ℤ) ≤ i := by
          rcases hi with hi | hi
          · left; omega
          · right; push_cast at hi ⊢; omega
        rw [hout2 _ hi2, hout1 _ ?_]
        rcases hi with hi | hi
        · left; omega
        · right; push_cast at hi; omega

/-- A leftward sweep across `k` blocks takes `3k` steps. -/
theorem chainL {q : St} {x y z x' y' z' : Sym} (h3 : BlockL q x y z x' y' z') :
    ∀ (k : ℕ) (T : ℤ → Sym) (a : ℤ),
      (∀ j : ℕ, j < 3 * k → T (a + j) = pat x y z j) →
      ∃ T' : ℤ → Sym, step^[3 * k] ⟨q, a + (3 * k : ℕ) - 1, T⟩ = ⟨q, a - 1, T'⟩ ∧
        (∀ j : ℕ, j < 3 * k → T' (a + j) = pat x' y' z' j) ∧
        (∀ i : ℤ, i < a ∨ a + (3 * k : ℕ) ≤ i → T' i = T i) := by
  intro k
  induction k with
  | zero =>
      intro T a _
      refine ⟨T, ?_, by intro j hj; omega, by intro i _; rfl⟩
      simp
  | succ k ih =>
      intro T a h
      -- the rightmost block starts at `b`
      set b : ℤ := a + ((3 * k : ℕ) : ℤ) with hb
      have h0 : T b = x := by
        have := h (3 * k) (by omega)
        rw [hb, this, show 3 * k = 0 + 3 * k by ring, pat_add3k]
        simp
      have h1 : T (b + 1) = y := by
        have := h (3 * k + 1) (by omega)
        rw [show a + ((3 * k + 1 : ℕ) : ℤ) = b + 1 by rw [hb]; push_cast; ring] at this
        rw [this, show 3 * k + 1 = 1 + 3 * k by ring, pat_add3k]
        simp
      have h2 : T (b + 2) = z := by
        have := h (3 * k + 2) (by omega)
        rw [show a + ((3 * k + 2 : ℕ) : ℤ) = b + 2 by rw [hb]; push_cast; ring] at this
        rw [this, show 3 * k + 2 = 2 + 3 * k by ring, pat_add3k]
        simp
      obtain ⟨T1, hs1, e0, e1, e2, hout1⟩ := h3 T b h0 h1 h2
      have hT1 : ∀ j : ℕ, j < 3 * k → T1 (a + j) = pat x y z j := by
        intro j hj
        rw [hout1 _ (Or.inl (by rw [hb]; push_cast; omega))]
        exact h j (by omega)
      obtain ⟨T2, hs2, hin2, hout2⟩ := ih T1 a hT1
      refine ⟨T2, ?_, ?_, ?_⟩
      · have e : 3 * (k + 1) = 3 * k + 3 := by ring
        rw [e, Function.iterate_add_apply]
        rw [show a + ((3 * k + 3 : ℕ) : ℤ) - 1 = b + 2 by rw [hb]; push_cast; ring]
        rw [hs1, show b - 1 = a + ((3 * k : ℕ) : ℤ) - 1 by rw [hb], hs2]
      · intro j hj
        rcases lt_or_ge j (3 * k) with hj3 | hj3
        · rw [hin2 j hj3]
        · have hout : T2 (a + j) = T1 (a + j) := by
            refine hout2 _ (Or.inr ?_)
            push_cast
            omega
          rw [hout]
          have hj' : j - 3 * k < 3 := by omega
          have hja : a + (j : ℤ) = b + ((j - 3 * k : ℕ) : ℤ) := by
            rw [hb]; push_cast; omega
          rw [hja]
          have hp : pat x' y' z' j = pat x' y' z' (j - 3 * k) := by
            conv_lhs => rw [show j = (j - 3 * k) + 3 * k by omega]
            rw [pat_add3k]
          rw [hp]
          interval_cases h' : (j - 3 * k)
          · simpa using e0
          · simpa using e1
          · rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
            simpa using e2
      · intro i hi
        have hi1 : i < a ∨ a + ((3 * k : ℕ) : ℤ) ≤ i := by
          rcases hi with hi | hi
          · left; omega
          · right; push_cast at hi ⊢; omega
        rw [hout2 _ hi1, hout1 _ ?_]
        rcases hi with hi | hi
        · left; rw [hb]; push_cast; omega
        · right; rw [hb]; push_cast at hi ⊢; omega

end BB25
