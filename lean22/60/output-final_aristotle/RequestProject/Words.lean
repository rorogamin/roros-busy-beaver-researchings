import RequestProject.Machine

/-!
# Tape words and macro rules

This file sets up the bookkeeping needed for *generalized* longitudinal analysis of
`1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`: instead of talking about individual cells, we talk
about *words* written on consecutive cells, and about *macro rules* of the form

> if the head sits at one end of a region carrying the word `u`, then after `n` steps it
> emerges at the other end, the region carries the word `v`, and nothing outside the
> region has changed.

Two such rules are recorded, `SweepR` (left-to-right) and `SweepL` (right-to-left), and
both compose: adjacent regions can be crossed one after the other.  All the concrete
macro rules of the development are built from a handful of primitive rules by these two
composition lemmas.
-/

namespace BB25

/-- `Seg T a w` says that the tape `T` carries the word `w` on the cells
`a, a+1, …, a + w.length - 1`. -/
def Seg (T : ℤ → Sym) (a : ℤ) (w : List Sym) : Prop :=
  ∀ i : ℕ, i < w.length → T (a + (i : ℤ)) = w.getD i 0

@[simp] lemma Seg_nil (T : ℤ → Sym) (a : ℤ) : Seg T a [] := by
  intro i hi; simp at hi

lemma Seg_cons {T : ℤ → Sym} {a : ℤ} {x : Sym} {w : List Sym} :
    Seg T a (x :: w) ↔ T a = x ∧ Seg T (a + 1) w := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    intro i hi
    have h' := h (i + 1) (by simpa using hi)
    have e : a + ((i + 1 : ℕ) : ℤ) = a + 1 + (i : ℤ) := by push_cast; ring
    rw [e] at h'
    simpa using h'
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
        have hi' : i < w.length := by simpa using hi
        have h' := h1 i hi'
        have e : a + ((i + 1 : ℕ) : ℤ) = a + 1 + (i : ℤ) := by push_cast; ring
        rw [e]
        simpa using h'

lemma Seg_append {T : ℤ → Sym} {a : ℤ} {u v : List Sym} :
    Seg T a (u ++ v) ↔ Seg T a u ∧ Seg T (a + (u.length : ℤ)) v := by
  induction u generalizing a with
  | nil => simp
  | cons x u ih =>
      rw [List.cons_append, Seg_cons, ih, Seg_cons]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨⟨h0, h1⟩, ?_⟩
        have e : a + 1 + (u.length : ℤ) = a + ((x :: u).length : ℤ) := by
          simp; ring
        rwa [e] at h2
      · rintro ⟨⟨h0, h1⟩, h2⟩
        refine ⟨h0, h1, ?_⟩
        have e : a + 1 + (u.length : ℤ) = a + ((x :: u).length : ℤ) := by
          simp; ring
        rwa [e]

/-- If two tapes agree on `[a, a + w.length)` then they carry the same words there. -/
lemma Seg_congr {T T' : ℤ → Sym} {a : ℤ} {w : List Sym}
    (h : ∀ i : ℕ, i < w.length → T' (a + (i : ℤ)) = T (a + (i : ℤ))) (hs : Seg T a w) :
    Seg T' a w := by
  intro i hi; rw [h i hi]; exact hs i hi

/-- `SweepR q q' u v n`: entering the region carrying `u` at its left end in state `q`,
the head leaves it at the right end in state `q'` after exactly `n` steps, the region now
carries `v`, and no cell outside the region has changed. -/
def SweepR (q q' : St) (u v : List Sym) (n : ℕ) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), Seg T a u →
    ∃ T' : ℤ → Sym,
      step^[n] ⟨q, a, T⟩ = ⟨q', a + (u.length : ℤ), T'⟩ ∧
      Seg T' a v ∧
      (∀ i : ℤ, i < a ∨ a + (u.length : ℤ) ≤ i → T' i = T i)

/-- `SweepL q q' u v n`: entering the region carrying `u` at its right end in state `q`,
the head leaves it at the left end in state `q'` after exactly `n` steps, the region now
carries `v`, and no cell outside the region has changed. -/
def SweepL (q q' : St) (u v : List Sym) (n : ℕ) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), Seg T a u →
    ∃ T' : ℤ → Sym,
      step^[n] ⟨q, a + (u.length : ℤ) - 1, T⟩ = ⟨q', a - 1, T'⟩ ∧
      Seg T' a v ∧
      (∀ i : ℤ, i < a ∨ a + (u.length : ℤ) ≤ i → T' i = T i)

/-- `Bounce q q' u v n`: the head enters the region carrying `u` at its **right** end,
moving left, and after exactly `n` steps comes back out on the **right** in state `q'`;
the region now carries `v` and nothing outside it has changed.  This is the macro rule
for a reflection off a wall, and it is what produces the triangles of the space-time
diagram. -/
def Bounce (q q' : St) (u v : List Sym) (n : ℕ) : Prop :=
  ∀ (T : ℤ → Sym) (a : ℤ), Seg T a u →
    ∃ T' : ℤ → Sym,
      step^[n] ⟨q, a + (u.length : ℤ) - 1, T⟩ = ⟨q', a + (u.length : ℤ), T'⟩ ∧
      Seg T' a v ∧
      (∀ i : ℤ, i < a ∨ a + (u.length : ℤ) ≤ i → T' i = T i)

/-- Two adjacent regions are crossed one after the other, left to right. -/
theorem SweepR.comp {q q' q'' : St} {u v u' v' : List Sym} {n n' : ℕ}
    (h : SweepR q q' u v n) (h' : SweepR q' q'' u' v' n')
    (hlen : v.length = u.length) :
    SweepR q q'' (u ++ u') (v ++ v') (n + n') := by
  intro T a hs
  rw [Seg_append] at hs
  obtain ⟨T1, hs1, hv1, hout1⟩ := h T a hs.1
  have hs2 : Seg T1 (a + (u.length : ℤ)) u' := by
    refine Seg_congr (fun i hi => ?_) hs.2
    exact hout1 _ (Or.inr (by omega))
  obtain ⟨T2, hs2', hv2, hout2⟩ := h' T1 (a + (u.length : ℤ)) hs2
  refine ⟨T2, ?_, ?_, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, hs1, hs2']
    have : a + (u.length : ℤ) + (u'.length : ℤ) = a + (((u ++ u').length : ℕ) : ℤ) := by
      simp; ring
    rw [this]
  · rw [Seg_append]
    refine ⟨?_, ?_⟩
    · refine Seg_congr (fun i hi => ?_) hv1
      exact hout2 _ (Or.inl (by rw [hlen] at hi; omega))
    · rw [hlen]; exact hv2
  · intro i hi
    simp only [List.length_append] at hi
    have hi1 : i < a + (u.length : ℤ) ∨ a + (u.length : ℤ) + (u'.length : ℤ) ≤ i := by
      rcases hi with hi | hi
      · left; omega
      · right; omega
    rw [hout2 _ hi1, hout1 _ ?_]
    rcases hi with hi | hi
    · left; omega
    · right; omega

/-- Two adjacent regions are crossed one after the other, right to left:
`h'` is the rule for the *right* region (entered first). -/
theorem SweepL.comp {q q' q'' : St} {u v u' v' : List Sym} {n n' : ℕ}
    (h' : SweepL q q' u' v' n') (h : SweepL q' q'' u v n)
    (hlen : v.length = u.length) :
    SweepL q q'' (u ++ u') (v ++ v') (n' + n) := by
  intro T a hs
  rw [Seg_append] at hs
  obtain ⟨T1, hs1, hv1, hout1⟩ := h' T (a + (u.length : ℤ)) hs.2
  have hpos : a + (((u ++ u').length : ℕ) : ℤ) - 1
      = (a + (u.length : ℤ)) + (u'.length : ℤ) - 1 := by
    simp; ring
  have hs2 : Seg T1 a u := by
    refine Seg_congr (fun i hi => ?_) hs.1
    exact hout1 _ (Or.inl (by omega))
  obtain ⟨T2, hs2', hv2, hout2⟩ := h T1 a hs2
  refine ⟨T2, ?_, ?_, ?_⟩
  · rw [hpos, Nat.add_comm, Function.iterate_add_apply, hs1, hs2']
  · rw [Seg_append]
    refine ⟨hv2, ?_⟩
    rw [hlen]
    refine Seg_congr (fun i hi => ?_) hv1
    exact hout2 _ (Or.inr (by omega))
  · intro i hi
    simp only [List.length_append] at hi
    have hi1 : i < a ∨ a + (u.length : ℤ) ≤ i := by
      rcases hi with hi | hi
      · left; omega
      · right; omega
    rw [hout2 _ hi1, hout1 _ ?_]
    rcases hi with hi | hi
    · left; omega
    · right; omega

/-- **Reflection.**  The head sweeps leftwards across the region `u'`, bounces off the
region `u` to its left, and sweeps rightwards across `u'` again.  The result is a bounce
off the combined region. -/
theorem Bounce.comp {q q1 q2 q3 : St} {u v u' v' v'' : List Sym} {n1 n2 n3 : ℕ}
    (h1 : SweepL q q1 u' v' n1) (h2 : Bounce q1 q2 u v n2) (h3 : SweepR q2 q3 v' v'' n3)
    (hlen : v.length = u.length) (hlen' : v'.length = u'.length) :
    Bounce q q3 (u ++ u') (v ++ v'') (n1 + n2 + n3) := by
  intro T a hs
  rw [Seg_append] at hs
  obtain ⟨hu, hu'⟩ := hs
  obtain ⟨T1, hs1, hv1, hout1⟩ := h1 T (a + (u.length : ℤ)) hu'
  have hu1 : Seg T1 a u := by
    refine Seg_congr (fun i hi => ?_) hu
    exact hout1 _ (Or.inl (by omega))
  obtain ⟨T2, hs2, hv2, hout2⟩ := h2 T1 a hu1
  have hv1' : Seg T2 (a + (u.length : ℤ)) v' := by
    refine Seg_congr (fun i hi => ?_) hv1
    exact hout2 _ (Or.inr (by omega))
  obtain ⟨T3, hs3, hv3, hout3⟩ := h3 T2 (a + (u.length : ℤ)) hv1'
  refine ⟨T3, ?_, ?_, ?_⟩
  · have hn : n1 + n2 + n3 = n3 + (n2 + n1) := by ring
    have hp : a + (((u ++ u').length : ℕ) : ℤ) - 1
        = (a + (u.length : ℤ)) + (u'.length : ℤ) - 1 := by simp; ring
    rw [hp, hn, Function.iterate_add_apply, Function.iterate_add_apply, hs1, hs2, hs3,
      hlen']
    simp
    ring
  · rw [Seg_append]
    refine ⟨?_, ?_⟩
    · refine Seg_congr (fun i hi => ?_) hv2
      refine hout3 _ (Or.inl ?_)
      rw [hlen] at hi
      omega
    · rw [hlen]; exact hv3
  · intro i hi
    simp only [List.length_append] at hi
    have hi3 : i < a + (u.length : ℤ) ∨ a + (u.length : ℤ) + ((v'.length : ℕ) : ℤ) ≤ i := by
      rcases hi with hi | hi
      · left; omega
      · right; rw [hlen']; push_cast at hi ⊢; omega
    rw [hout3 _ hi3]
    have hi2 : i < a ∨ a + (u.length : ℤ) ≤ i := by
      rcases hi with hi | hi
      · left; omega
      · right; push_cast at hi ⊢; omega
    rw [hout2 _ hi2]
    refine hout1 _ ?_
    rcases hi with hi | hi
    · left; omega
    · right; push_cast at hi ⊢; omega

end BB25
