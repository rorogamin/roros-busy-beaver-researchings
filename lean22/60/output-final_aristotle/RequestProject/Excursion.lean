import RequestProject.Bounces
import RequestProject.NonHalting

/-!
# Macro rules certify non-halting, and a complete left-to-right excursion

Two things are collected here.

1. A macro rule automatically certifies that the machine does **not** halt at any of the
   intermediate steps it covers: the halting state is absorbing, so a rule whose final
   state is `A` or `B` cannot have passed through `H` (`SweepR.no_halt`, `SweepL.no_halt`,
   `Bounce.no_halt`).

2. `left_end_sweep`: starting from the configuration in which the head, in state `A`,
   stands on a blank cell with a blank to its left and an arbitrary sequence of blocks
   `0 4^{j₁} 2 … 0 4^{jₘ} 2` to its right — which is exactly the shape of the tape each
   time the head reaches a new leftmost cell — the machine writes `1 3` at the left end
   and then crosses the whole block sequence in one pass, in `5 + ∑ (jᵢ + 2)` steps,
   without halting.
-/

namespace BB25

/-! ### No halting inside a macro rule -/

/-- Once halted, always halted (for an arbitrary starting configuration). -/
lemma halted_iterate {c : Cfg} {m n : ℕ} (hmn : m ≤ n) (h : Halted (step^[m] c)) :
    Halted (step^[n] c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have e : step^[m + (k + 1)] c = step (step^[m + k] c) := by
        rw [show m + (k + 1) = (m + k) + 1 by ring, Function.iterate_succ_apply']
      rw [e]
      exact halted_step ih

lemma not_halted_within {c : Cfg} {n : ℕ} (h : ¬ Halted (step^[n] c)) :
    ∀ m ≤ n, ¬ Halted (step^[m] c) := fun _ hm hc => h (halted_iterate hm hc)

/-- A rightward macro rule certifies that the machine does not halt during the steps it
covers. -/
theorem SweepR.no_halt {q q' : St} {u v : List Sym} {n : ℕ} (h : SweepR q q' u v n)
    (hq : q' ≠ St.H) (T : ℤ → Sym) (a : ℤ) (hs : Seg T a u) :
    ∀ m ≤ n, ¬ Halted (step^[m] ⟨q, a, T⟩) := by
  obtain ⟨T', hs', -, -⟩ := h T a hs
  exact not_halted_within (by rw [Halted, hs']; exact hq)

/-- A leftward macro rule certifies that the machine does not halt during the steps it
covers. -/
theorem SweepL.no_halt {q q' : St} {u v : List Sym} {n : ℕ} (h : SweepL q q' u v n)
    (hq : q' ≠ St.H) (T : ℤ → Sym) (a : ℤ) (hs : Seg T a u) :
    ∀ m ≤ n, ¬ Halted (step^[m] ⟨q, a + (u.length : ℤ) - 1, T⟩) := by
  obtain ⟨T', hs', -, -⟩ := h T a hs
  exact not_halted_within (by rw [Halted, hs']; exact hq)

/-- A bounce certifies that the machine does not halt during the steps it covers. -/
theorem Bounce.no_halt {q q' : St} {u v : List Sym} {n : ℕ} (h : Bounce q q' u v n)
    (hq : q' ≠ St.H) (T : ℤ → Sym) (a : ℤ) (hs : Seg T a u) :
    ∀ m ≤ n, ¬ Halted (step^[m] ⟨q, a + (u.length : ℤ) - 1, T⟩) := by
  obtain ⟨T', hs', -, -⟩ := h T a hs
  exact not_halted_within (by rw [Halted, hs']; exact hq)

/-! ### A complete excursion from the left end -/

lemma wordIn_head {j : ℕ} {js : List ℕ} : (wordIn (j :: js)).getD 0 0 = 0 := by
  rw [wordIn_cons]
  rfl

/-- **From the left end across the whole tape.**  The head is in state `A` on a blank
cell `p`, the cell `p - 1` is blank as well, and the cells from `p + 1` on carry an
arbitrary sequence of blocks `0 4^{j} 2`.  Then in exactly `5 + ∑ (jᵢ + 2)` steps the
machine writes `1 3` on the cells `p - 1, p`, turns every block `0 4^{j} 2` into
`1 0^{j} 3`, and arrives in state `A` just past the last block. -/
theorem left_end_sweep (j : ℕ) (js : List ℕ) (T : ℤ → Sym) (p : ℤ)
    (hm : T (p - 1) = 0) (h0 : T p = 0) (hseg : Seg T (p + 1) (wordIn (j :: js))) :
    ∃ T' : ℤ → Sym,
      step^[5 + cost (j :: js)] ⟨St.A, p, T⟩
        = ⟨St.A, p + 1 + ((wordIn (j :: js)).length : ℤ), T'⟩ ∧
      T' (p - 1) = 1 ∧ T' p = 3 ∧ Seg T' (p + 1) (wordOut (j :: js)) ∧
      (∀ i : ℤ, i < p - 1 ∨ p + 1 + ((wordIn (j :: js)).length : ℤ) ≤ i → T' i = T i) := by
  have hlen : 0 < (wordIn (j :: js)).length := by
    rw [wordIn_cons]; simp
  have h1 : T (p + 1) = 0 := by
    have := hseg 0 hlen
    simpa [wordIn_head] using this
  -- the left-end extension
  have hext := left_blank_extend T p hm h0 h1
  set T1 := wr (wr T (p - 1) 1) p 3 with hT1
  have hT1out : ∀ i : ℤ, i ≠ p - 1 → i ≠ p → T1 i = T i := by
    intro i hi hi'
    rw [hT1, wr_of_ne _ _ _ hi', wr_of_ne _ _ _ hi]
  have hseg1 : Seg T1 (p + 1) (wordIn (j :: js)) := by
    refine Seg_congr (fun i _ => ?_) hseg
    exact hT1out _ (by omega) (by omega)
  obtain ⟨T2, hs2, hv2, hout2⟩ := sweepR_blocks (j :: js) T1 (p + 1) hseg1
  refine ⟨T2, ?_, ?_, ?_, hv2, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, hext, hs2]
  · rw [hout2 _ (Or.inl (by omega)), hT1, wr_of_ne _ _ _ (by omega), wr_self]
  · rw [hout2 _ (Or.inl (by omega)), hT1, wr_self]
  · intro i hi
    have hi2 : i < p + 1 ∨ p + 1 + ((wordIn (j :: js)).length : ℤ) ≤ i := by
      rcases hi with hi | hi
      · left; omega
      · right; omega
    rw [hout2 _ hi2]
    refine hT1out _ ?_ ?_ <;> rcases hi with hi | hi <;> omega

/-- The machine does not halt at any point of such an excursion. -/
theorem left_end_sweep_no_halt (j : ℕ) (js : List ℕ) (T : ℤ → Sym) (p : ℤ)
    (hm : T (p - 1) = 0) (h0 : T p = 0) (hseg : Seg T (p + 1) (wordIn (j :: js))) :
    ∀ m ≤ 5 + cost (j :: js), ¬ Halted (step^[m] ⟨St.A, p, T⟩) := by
  obtain ⟨T', hs', -, -, -, -⟩ := left_end_sweep j js T p hm h0 hseg
  exact not_halted_within (by rw [Halted, hs']; exact fun h => St.noConfusion h)

end BB25
