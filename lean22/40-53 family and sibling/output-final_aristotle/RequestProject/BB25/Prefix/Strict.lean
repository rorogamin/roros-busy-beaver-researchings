/-
# Strict admissibility

A counter stack is *strictly admissible* when no bottom prefix of it pops its
bottommost unmatched bit — equivalently, when every bottom prefix that contains
a bit has strictly more bits than pops.

Every nonempty clean paid reset is strictly admissible (`Strict.tfold`),
because a reset pop needs a counter of at least two and so at least two
unmatched bits below it.  This is the extra invariant the `0RB` return needs:
goodness, positivity, `X`-ending and readiness alone are not enough for `0RB`
(the submitted document exhibits the good, positive, `X`-ending and ready stack
`ZWZZXWX`, on which `0RB` runs into the undefined transition `A4`; its bottom
`ZW` closes the bottommost bit).
-/
import RequestProject.BB25.Prefix.Drain
import RequestProject.BB25.Prefix.Main

namespace BB25.Prefix

open BB25

/-! ## The predicate -/

/-- **Strict admissibility**: every bottom prefix that contains a bit has
strictly more bits than pops.  For an admissible stack this says exactly that
no bottom prefix pops the bottommost unmatched bit. -/
def Strict (s : List LB) : Prop := ∀ t, t <:+ s → 1 ≤ nbit t → nsh t + 1 ≤ nbit t

theorem Strict.suffix {s t : List LB} (h : Strict s) (ht : t <:+ s) : Strict t :=
  fun u hu => h u (hu.trans ht)

theorem Strict.head {s : List LB} (h : Strict s) (hb : 1 ≤ nbit s) : nsh s + 1 ≤ nbit s :=
  h s (List.suffix_refl s) hb

theorem strict_L : Strict [LB.L] := by
  intro t ht hb
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · simp at hb
  · obtain rfl : t = [] := List.eq_nil_of_suffix_nil ht'
    simp at hb

theorem Strict.cons {b : LB} {s : List LB} (h : Strict s)
    (hb : 1 ≤ nbit (b :: s) → nsh (b :: s) + 1 ≤ nbit (b :: s)) : Strict (b :: s) := by
  intro t ht
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · exact hb
  · exact h t ht'

theorem strict_consZ {s : List LB} (hadm : Adm s) (h : Strict s) : Strict (.Z :: s) :=
  h.cons (fun _ => by simpa using hadm.head)

theorem strict_consX {s : List LB} (hadm : Adm s) (h : Strict s) : Strict (.X :: s) :=
  h.cons (fun _ => by simpa using hadm.head)

theorem strict_consW {s : List LB} (h : Strict s) (hc : nsh s + 2 ≤ nbit s) :
    Strict (.W :: s) :=
  h.cons (fun _ => by simpa using by omega)

/-- The decrement preserves strict admissibility. -/
theorem Strict.cdec {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) (h : Strict s) :
    Strict (cdec s) := by
  intro v hvs hb
  obtain ⟨u, hu, -, -, h3, h4⟩ := cdec_suffix hst hv hvs
  rw [h3, h4]
  exact h u hu (by omega)

/-- A run of zero bits above a strictly admissible stack is strictly
admissible. -/
theorem Strict_Zrun : ∀ (r : ℕ) {s : List LB}, Adm s → Strict s →
    Strict (List.replicate r .Z ++ s) := by
  intro r
  induction r with
  | zero => intro s _ h; simpa using h
  | succ r ih =>
      intro s hadm h
      rw [List.replicate_succ, List.cons_append]
      exact strict_consZ (Adm_Zrun r hadm) (ih hadm h)

/-! ## Strict admissibility of a paid reset -/

/-- One digit of a clean reset preserves strict admissibility. -/
theorem Strict.tstep {σ : List LB} {b : RB} (hb : Dig b) (hst : CStack σ) (hadm : Adm σ)
    (h : Strict σ) (hcl : 0 ≤ rstep b (cval σ)) : Strict (tstep σ b) := by
  rcases hb with rfl | rfl | rfl
  · exact strict_consZ hadm h
  · exact strict_consX hadm h
  · -- a reset pop needs a counter of at least two, hence two unmatched bits
    have ha2 : 2 ≤ cval σ := by
      simp only [rstep_X] at hcl
      omega
    have hcount : 2 ≤ nbit σ - nsh σ := two_le_unmatched hst hadm ha2
    have hadmh := hadm.head
    have hW : Strict (.W :: σ) := strict_consW h (by omega)
    have hWv : 1 ≤ cval (.W :: σ) := by
      simp only [cval_W]
      omega
    exact (hW.cdec hst.consW hWv)

/-- **A clean paid reset above a strictly admissible stack is strictly
admissible.** -/
theorem Strict.tfold : ∀ (w : List RB), Digs w → ∀ {σ : List LB}, CStack σ → Adm σ → Good σ →
    Strict σ → 0 ≤ rrun w (cval σ) → Strict (tfold σ w) := by
  intro w
  induction w with
  | nil => intro _ σ _ _ _ h _; exact h
  | cons b w ih =>
      intro hw σ hst hadm hg hstr hcl
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have hcl1 : 0 ≤ rstep b (cval σ) := by
        have := rrun_nonneg_of_nonneg (w := [b]) (v := w) hw' (a := (cval σ : ℤ))
          (by simpa using hcl)
        simpa using this
      obtain ⟨hst1, hadm1, hg1, hcv1, -, -⟩ := tstep_props hb hst hadm hg hcl1
      refine ih hw' hst1 hadm1 hg1 (Strict.tstep hb hst hadm hstr hcl1) ?_
      rw [hcv1]
      simpa using hcl

/-- **A clean paid reset from the empty stack is strictly admissible.** -/
theorem strict_TW {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0) :
    Strict (tfold [LB.L] w) :=
  Strict.tfold w hw CStack.base adm_L good_L strict_L (by simpa using hcl)

/-- The seed checkpoint of the family is strictly admissible. -/
theorem strict_seedStack : Strict seedStack := by
  have hL : Strict [LB.L] := strict_L
  have h1 : Strict [LB.Z, LB.L] := strict_consZ adm_L hL
  have h2 : Strict [LB.Z, LB.Z, LB.L] := strict_consZ (adm_consZ adm_L) h1
  have h3 : Strict [LB.Z, LB.Z, LB.Z, LB.L] :=
    strict_consZ (adm_consZ (adm_consZ adm_L)) h2
  have h4 : Strict [LB.X, LB.Z, LB.Z, LB.Z, LB.L] :=
    strict_consX (adm_consZ (adm_consZ (adm_consZ adm_L))) h3
  have h5 : Strict [LB.X, LB.X, LB.Z, LB.Z, LB.Z, LB.L] :=
    strict_consX (adm_consX (adm_consZ (adm_consZ (adm_consZ adm_L)))) h4
  exact strict_consX (adm_consX (adm_consX (adm_consZ (adm_consZ (adm_consZ adm_L))))) h5

end BB25.Prefix
