import RequestProject.Epoch
import RequestProject.Pair

/-!
# Non-halting of `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---`

The two-epoch argument, assembled:

* `blank_to_seed`: from the blank tape the machine reaches the normal overflow
  configuration `⟨L, ovfWord5, [3,2]⟩` after `4011` steps;
* `reach_iter`: the exact epoch law `epoch_step` carries it through seven more
  overflows, to an overflow word whose chunk word is `T⁷ (ck ovfWord5)`;
* `base_good`: that chunk word and the next one are `Good` (a finite check);
* `good_pair` propagates the invariant, and `epoch_step` turns every step of
  the propagation into a positive number of real machine steps.

Hence `not_halts : ¬ Halts`.
-/

namespace BB25


set_option maxRecDepth 200000

/-! ## The finite entry -/

/-- The word at the 5th overflow of the orbit from the blank tape. -/
def ovfWord5 : List Tok :=
  [.P, .P, .P, .P, .P, .P, .F, .P, .C, .C, .C, .P, .P, .P, .C, .C, .C, .F, .F, .F, .C]

/-- **The blank tape reaches the 5th overflow** after `4011` steps. -/
theorem blank_to_seed : steps 4011 init = some (ecfg ⟨.L, ovfWord5, [3, 2]⟩) := by
  rfl

theorem ovfWord5_cap : cap ovfWord5 = 0 := by decide

/-- A decidable check that `n` successive epochs from a chunk word are all
defined (each scan succeeds with value at least `3`). -/
def okIter : ℕ → List Ck → Bool
  | 0, _ => true
  | n + 1, c => (match ckFold 0 c with
      | some v => decide (3 ≤ v)
      | none => false) && okIter n (epochMap c)

/-- **Iterating the epoch law.** -/
theorem reach_iter : ∀ (n : ℕ) (X : List Tok), cap X = 0 → okIter n (ck X) = true →
    ∃ X', cap X' = 0 ∧ ck X' = epochMap^[n] (ck X) ∧ Reaches ⟨.L, X, [3, 2]⟩ ⟨.L, X', [3, 2]⟩ := by
  intro n
  induction n with
  | zero => intro X hX _; exact ⟨X, hX, rfl, Reaches.refl _⟩
  | succ n ih =>
      intro X hX hok
      simp only [okIter, Bool.and_eq_true] at hok
      obtain ⟨h1, h2⟩ := hok
      cases hv : ckFold 0 (ck X) with
      | none => rw [hv] at h1; exact absurd h1 (by simp)
      | some v =>
          rw [hv] at h1
          have h3 : 3 ≤ v := by simpa using h1
          obtain ⟨X1, hX1, hck1, hrun1⟩ := epoch_step X hX v hv h3
          rw [← hck1] at h2
          obtain ⟨X2, hX2, hck2, hrun2⟩ := ih X1 hX1 h2
          refine ⟨X2, hX2, ?_, ?_⟩
          · rw [hck2, hck1, Function.iterate_succ_apply]
          · obtain ⟨t, -, ht⟩ := hrun1
            exact Reaches.trans ⟨t, ht⟩ hrun2

/-- The chunk word at the 12th overflow. -/
def base12 : List Ck := epochMap^[7] (ck ovfWord5)

theorem ok_to_12 : okIter 7 (ck ovfWord5) = true := by decide +kernel

/-- A decidable form of `Good`. -/
def goodB (c : List Ck) : Bool :=
  decide (Phi c ≤ eps) && decide (c = c.take (c.length - 12) ++ List.replicate 12 Ck.S) &&
    decide (8 ≤ conv 0 c)

theorem good_of_goodB (c : List Ck) (h : goodB c = true) : Good c := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, ⟨_, h.1.2⟩, h.2⟩

/-- **The base pair**: the chunk words at the 12th and 13th overflows are
`Good`. -/
theorem base_good : Good base12 ∧ Good (epochMap base12) :=
  ⟨good_of_goodB _ (by decide +kernel), good_of_goodB _ (by decide +kernel)⟩

/-! ## The infinite induction -/

/-- **The machine runs forever**: for every `n` it reaches, at some time
`t ≥ n`, a normal overflow configuration whose chunk word and its successor
are `Good`. -/
theorem forever : ∀ n : ℕ, ∃ X : List Tok, cap X = 0 ∧ Good (ck X) ∧ Good (epochMap (ck X)) ∧
    ∃ t, n ≤ t ∧ steps t init = some (ecfg ⟨.L, X, [3, 2]⟩) := by
  intro n
  induction n with
  | zero =>
      obtain ⟨X, hX, hck, t, ht⟩ := reach_iter 7 ovfWord5 ovfWord5_cap ok_to_12
      refine ⟨X, hX, ?_, ?_, 4011 + t, Nat.zero_le _, steps_trans blank_to_seed ht⟩
      · rw [hck]; exact base_good.1
      · rw [hck]; exact base_good.2
  | succ n ih =>
      obtain ⟨X, hX, hg1, hg2, t, htn, ht⟩ := ih
      obtain ⟨v, hv, h3⟩ := good_scan _ hg1
      obtain ⟨X', hX', hck, s, hs, hrun⟩ := epoch_step X hX v hv h3
      refine ⟨X', hX', ?_, ?_, t + s, by omega, steps_trans ht hrun⟩
      · rw [hck]; exact hg2
      · rw [hck]; exact good_pair _ hg1 hg2

/-- **`1RB3LA3LA0RB2LB_2LA4LA4RA2RA---` does not halt** from the blank tape. -/
theorem not_halts : ¬ Halts := by
  rintro ⟨n, hn⟩
  obtain ⟨X, -, -, -, t, htn, ht⟩ := forever n
  have : steps t init = none := by
    rw [show t = n + (t - n) by omega, steps_add, hn]; rfl
  rw [this] at ht
  exact absurd ht (by simp)

end BB25
