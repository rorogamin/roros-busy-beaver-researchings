/-
# The paid reset stack

While the machine re-parses a word of digit blocks it builds a counter stack.
The pending digit `1>` carries a debt of one decrement, which the machine pays
at the next turn.  `tstep`/`tfold` describe the stack *after* that payment —
the **paid reset stack** of the word:

```
  Y ↦ push the bit 1 (Z)      V ↦ push the bit 0 (X)      X ↦ pop (W), then pay
```

`tfold_props` is the arithmetic of the construction: the counter of the paid
stack is the reset value `rrun` of the word, its decoded value is the
transduced value `trun`, and — this is the invariant of the whole development —
the paid stack is always good and admissible.

`brun_paid` is the machine correspondence: the block machine really does
re-parse the word and end with the paid stack (up to the pending debt).
-/
import RequestProject.BB25.Prefix.Stack
import RequestProject.BB25.Runs

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The paid reset stack -/

/-- One digit of the reset, as an operation on the paid stack. -/
def tstep (σ : List LB) : RB → List LB
  | .Y => .Z :: σ
  | .V => .X :: σ
  | .X => cdec (.W :: σ)
  | _ => σ

@[simp] theorem tstep_Y (σ : List LB) : tstep σ .Y = .Z :: σ := rfl
@[simp] theorem tstep_V (σ : List LB) : tstep σ .V = .X :: σ := rfl
@[simp] theorem tstep_X (σ : List LB) : tstep σ .X = cdec (.W :: σ) := rfl

/-- The paid stack built by a whole word. -/
def tfold : List LB → List RB → List LB
  | σ, [] => σ
  | σ, b :: w => tfold (tstep σ b) w

@[simp] theorem tfold_nil (σ : List LB) : tfold σ [] = σ := rfl
@[simp] theorem tfold_cons (σ : List LB) (b : RB) (w : List RB) :
    tfold σ (b :: w) = tfold (tstep σ b) w := rfl

theorem tfold_append (σ : List LB) (w v : List RB) :
    tfold σ (w ++ v) = tfold (tfold σ w) v := by
  induction w generalizing σ with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- The counter of the paid stack after one digit. -/
theorem tstep_cval {σ : List LB} {b : RB} (hb : Dig b) (hst : CStack σ)
    (hcl : 0 ≤ rstep b (cval σ)) : (cval (tstep σ b) : ℤ) = rstep b (cval σ) := by
  rcases hb with rfl | rfl | rfl
  · simp
  · simp
  · have ha2 : 2 ≤ cval σ := by
      simp only [rstep_X] at hcl
      omega
    have hWv : 1 ≤ cval (.W :: σ) := by simp only [cval_W]; omega
    simp only [tstep_X, rstep_X]
    rw [cdec_cval hst.consW hWv]
    simp only [cval_W]
    omega

/-- **One digit of the reset.** -/
theorem tstep_props {σ : List LB} {b : RB} (hb : Dig b) (hst : CStack σ) (hadm : Adm σ)
    (hg : Good σ) (hcl : 0 ≤ rstep b (cval σ)) :
    CStack (tstep σ b) ∧ Adm (tstep σ b) ∧ Good (tstep σ b) ∧
      (cval (tstep σ b) : ℤ) = rstep b (cval σ) ∧
      bval (tstep σ b) = rstep (qout b (cval σ)) (bval σ) ∧
      1 ≤ nbit (tstep σ b) - nsh (tstep σ b) := by
  have hgb : (cval σ : ℤ) ≤ bval σ := hg.head
  rcases hb with rfl | rfl | rfl
  · -- Y : push the bit 1
    have hadmh := hadm.head
    refine ⟨hst.consZ, hadm.cons ?_, hg.cons ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp
    · simp [qout]
    · simp; omega
  · -- V : push the bit 0
    have hadmh := hadm.head
    refine ⟨hst.consX, hadm.cons ?_, hg.cons ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp
    · simp [qout]
    · simp; omega
  · -- X : pop, and pay the pending decrement
    have ha2 : 2 ≤ cval σ := by
      simp only [rstep_X] at hcl
      omega
    have hcount : 2 ≤ nbit σ - nsh σ := two_le_unmatched hst hadm ha2
    have hWv : 1 ≤ cval (.W :: σ) := by
      simp only [cval_W]
      omega
    have hWst : CStack (.W :: σ) := hst.consW
    have hWadm : Adm (.W :: σ) := hadm.cons (by simp; omega)
    have hcst : CStack (cdec (.W :: σ)) := cdec_CStack_all hWst
    have hcadm : Adm (cdec (.W :: σ)) := Adm.cdec hWst hWadm hWv
    have hcv : cval (cdec (.W :: σ)) = cval (.W :: σ) - 1 := cdec_cval hWst hWv
    have hbv : bval (cdec (.W :: σ)) = bval (.W :: σ) := bval_cdec hWst hWv
    -- goodness of the popped stack
    have hv1 : 1 ≤ cval σ := by omega
    have hg1 : Good (cdec σ) := Good.cdec hst hg hv1
    have hst1 : CStack (cdec σ) := cdec_CStack_all hst
    have hc1 : cval (cdec σ) = cval σ - 1 := cdec_cval hst hv1
    have hv2 : 1 ≤ cval (cdec σ) := by omega
    have hg2 : Good (cdec (cdec σ)) := Good.cdec hst1 hg1 hv2
    have hgood : Good (cdec (.W :: σ)) := by
      rw [cdec_W]
      refine hg2.cons ?_
      have hb1 : bval (cdec (cdec σ)) = bval σ := by
        rw [bval_cdec hst1 hv2, bval_cdec hst hv1]
      have hc2 : cval (cdec (cdec σ)) = cval σ - 2 := by
        rw [cdec_cval hst1 hv2, hc1]
        omega
      have hpar : (cval σ - 2) % 2 = cval σ % 2 := by omega
      simp only [cval_W, bval_W, hc2, hb1, hpar]
      by_cases hodd : cval σ % 2 = 1
      · simp only [hodd, if_pos]
        omega
      · simp only [hodd, if_false]
        omega
    have hcvX : cval (tstep σ .X) = cval σ / 2 - 1 := by
      rw [tstep_X, hcv]
      rfl
    refine ⟨hcst, hcadm, hgood, ?_, ?_, ?_⟩
    · rw [hcvX, rstep_X]
      omega
    · simp only [tstep_X, hbv, bval_W, qout]
      by_cases hodd : cval σ % 2 = 1
      · have : (cval σ : ℤ) % 2 = 1 := by omega
        simp [hodd, this]
      · have : (cval σ : ℤ) % 2 ≠ 1 := by omega
        simp [hodd, this]
    · simp only [tstep_X]
      rw [nbit_cdec, nsh_cdec]
      simp
      omega

/-- **The paid reset stack of a whole clean word.** -/
theorem tfold_props : ∀ (w : List RB), Digs w → ∀ {σ : List LB}, CStack σ → Adm σ → Good σ →
    0 ≤ rrun w (cval σ) →
    CStack (tfold σ w) ∧ Adm (tfold σ w) ∧ Good (tfold σ w) ∧
      (cval (tfold σ w) : ℤ) = rrun w (cval σ) ∧
      bval (tfold σ w) = trun w (cval σ) (bval σ) ∧
      (w ≠ [] → 1 ≤ nbit (tfold σ w) - nsh (tfold σ w)) := by
  intro w
  induction w with
  | nil =>
      intro _ σ hst hadm hg _
      exact ⟨hst, hadm, hg, rfl, rfl, by simp⟩
  | cons b w ih =>
      intro hw σ hst hadm hg hcl
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have hcl1 : 0 ≤ rstep b (cval σ) := by
        have := rrun_nonneg_of_nonneg (w := [b]) (v := w) hw' (a := (cval σ : ℤ))
          (by simpa using hcl)
        simpa using this
      obtain ⟨hst1, hadm1, hg1, hcv1, hbv1, hcount1⟩ := tstep_props hb hst hadm hg hcl1
      have hcl2 : 0 ≤ rrun w (cval (tstep σ b)) := by rw [hcv1]; simpa using hcl
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hw' hst1 hadm1 hg1 hcl2
      refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
      · rw [tfold_cons, h4, hcv1, rrun_cons]
      · rw [tfold_cons, h5, hcv1, hbv1, trun_cons]
      · intro _
        rcases eq_or_ne w [] with rfl | hne
        · simpa using hcount1
        · exact h6 hne

/-! ## The machine correspondence -/

/-- The paid stack of a physical configuration: with a pending `1>` one
decrement is still owed. -/
def paid (p : Bool) (σ : List LB) : List LB := if p then σ else cdec σ

@[simp] theorem paid_true (σ : List LB) : paid true σ = σ := rfl
@[simp] theorem paid_false (σ : List LB) : paid false σ = cdec σ := rfl

/-- **The machine re-parses a clean word and ends with its paid reset stack.** -/
theorem brun_paid : ∀ (w : List RB), Digs w → ∀ (p : Bool) (σ : List LB), CStack σ →
    (p = false → 1 ≤ cval σ) → 0 ≤ rrun w (cval (paid p σ)) → ∀ rest : List RB,
      ∃ (p' : Bool) (phys : List LB) (k : ℕ),
        BRun b4 ⟨σ, .Rt, pd p :: (w ++ rest)⟩ ⟨phys, .Rt, pd p' :: rest⟩ k ∧
          CStack phys ∧ paid p' phys = tfold (paid p σ) w ∧
          (p' = false → cval phys = cval (tfold (paid p σ) w) + 1) := by
  intro w
  induction w with
  | nil =>
      intro _ p σ hst hp _ rest
      refine ⟨p, σ, 0, by simpa using BRun.refl (b4 := b4) _, hst, rfl, ?_⟩
      intro hpf
      subst hpf
      have h1 : 1 ≤ cval σ := hp rfl
      simp only [paid_false, tfold_nil]
      rw [cdec_cval hst h1]
      omega
  | cons b w ih =>
      intro hw p σ hst hp hcl rest
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have hcl1 : 0 ≤ rstep b (cval (paid p σ)) := by
        have := rrun_nonneg_of_nonneg (w := [b]) (v := w) hw' (a := (cval (paid p σ) : ℤ))
          (by simpa using hcl)
        simpa using this
      -- one digit of the machine
      have key : ∃ (p₁ : Bool) (phys₁ : List LB) (k₁ : ℕ),
          BRun b4 ⟨σ, .Rt, pd p :: (b :: (w ++ rest))⟩ ⟨phys₁, .Rt, pd p₁ :: (w ++ rest)⟩ k₁ ∧
            CStack phys₁ ∧ paid p₁ phys₁ = tstep (paid p σ) b ∧
            (p₁ = false → cval phys₁ = cval (tstep (paid p σ) b) + 1) := by
        cases p with
        | true =>
            rcases hb with rfl | rfl | rfl
            · refine ⟨true, .Z :: σ, 0 + 2, ?_, hst.consZ, rfl, by simp⟩
              exact BRun.head (show bstep b4 ⟨σ, .Rt, .P2 :: .Y :: (w ++ rest)⟩
                  = some (⟨σ, .Rt, .Y :: .P2 :: (w ++ rest)⟩, 0) from rfl)
                (BRun.of_step (show bstep b4 ⟨σ, .Rt, .Y :: .P2 :: (w ++ rest)⟩
                  = some (⟨.Z :: σ, .Rt, .P2 :: (w ++ rest)⟩, 2) from rfl))
            · refine ⟨false, .Z :: σ, 0 + 2, ?_, hst.consZ, by simp, by simp⟩
              exact BRun.head (show bstep b4 ⟨σ, .Rt, .P2 :: .V :: (w ++ rest)⟩
                  = some (⟨σ, .Rt, .Y :: .P1 :: (w ++ rest)⟩, 0) from rfl)
                (BRun.of_step (show bstep b4 ⟨σ, .Rt, .Y :: .P1 :: (w ++ rest)⟩
                  = some (⟨.Z :: σ, .Rt, .P1 :: (w ++ rest)⟩, 2) from rfl))
            · have ha2 : 2 ≤ cval σ := by
                simp only [paid_true, rstep_X] at hcl1
                omega
              have hWv : 1 ≤ cval (.W :: σ) := by simp only [cval_W]; omega
              refine ⟨false, .W :: σ, 0 + 2, ?_, hst.consW, by simp, ?_⟩
              · exact BRun.head (show bstep b4 ⟨σ, .Rt, .P2 :: .X :: (w ++ rest)⟩
                    = some (⟨σ, .Rt, .V :: .P1 :: (w ++ rest)⟩, 0) from rfl)
                  (BRun.of_step (show bstep b4 ⟨σ, .Rt, .V :: .P1 :: (w ++ rest)⟩
                    = some (⟨.W :: σ, .Rt, .P1 :: (w ++ rest)⟩, 2) from rfl))
              · intro _
                simp only [paid_true, tstep_X]
                rw [cdec_cval hst.consW hWv]
                omega
        | false =>
            have hv1 : 1 ≤ cval σ := hp rfl
            have hst1 : CStack (cdec σ) := cdec_CStack_all hst
            rcases hb with rfl | rfl | rfl
            · obtain ⟨k, hrun⟩ := brun_cdec_of (b4 := b4) hst hv1 (.Y :: .P2 :: (w ++ rest))
              refine ⟨true, .Z :: cdec σ, 0 + (1 + (k + 2)), ?_, hst1.consZ, rfl, by simp⟩
              exact BRun.head (show bstep b4 ⟨σ, .Rt, .P1 :: .Y :: (w ++ rest)⟩
                  = some (⟨σ, .Rt, .U :: .P2 :: (w ++ rest)⟩, 0) from rfl)
                (BRun.head (show bstep b4 ⟨σ, .Rt, .U :: .P2 :: (w ++ rest)⟩
                    = some (⟨σ, .Lt, .Y :: .P2 :: (w ++ rest)⟩, 1) from rfl)
                  (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec σ, .Rt, .Y :: .P2 :: (w ++ rest)⟩
                    = some (⟨.Z :: cdec σ, .Rt, .P2 :: (w ++ rest)⟩, 2) from rfl))))
            · obtain ⟨k, hrun⟩ := brun_cdec_of (b4 := b4) hst hv1 (.Y :: .P1 :: (w ++ rest))
              refine ⟨false, .Z :: cdec σ, 0 + (1 + (k + 2)), ?_, hst1.consZ, by simp, by simp⟩
              exact BRun.head (show bstep b4 ⟨σ, .Rt, .P1 :: .V :: (w ++ rest)⟩
                  = some (⟨σ, .Rt, .U :: .P1 :: (w ++ rest)⟩, 0) from rfl)
                (BRun.head (show bstep b4 ⟨σ, .Rt, .U :: .P1 :: (w ++ rest)⟩
                    = some (⟨σ, .Lt, .Y :: .P1 :: (w ++ rest)⟩, 1) from rfl)
                  (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec σ, .Rt, .Y :: .P1 :: (w ++ rest)⟩
                    = some (⟨.Z :: cdec σ, .Rt, .P1 :: (w ++ rest)⟩, 2) from rfl))))
            · have ha2 : 2 ≤ cval (cdec σ) := by
                simp only [paid_false, rstep_X] at hcl1
                omega
              have hWv : 1 ≤ cval (.W :: cdec σ) := by simp only [cval_W]; omega
              obtain ⟨k, hrun⟩ := brun_cdec_of (b4 := b4) hst hv1 (.V :: .P1 :: (w ++ rest))
              refine ⟨false, .W :: cdec σ, 0 + (1 + (k + 2)), ?_, hst1.consW, by simp, ?_⟩
              · exact BRun.head (show bstep b4 ⟨σ, .Rt, .P1 :: .X :: (w ++ rest)⟩
                    = some (⟨σ, .Rt, .X :: .P1 :: (w ++ rest)⟩, 0) from rfl)
                  (BRun.head (show bstep b4 ⟨σ, .Rt, .X :: .P1 :: (w ++ rest)⟩
                      = some (⟨σ, .Lt, .V :: .P1 :: (w ++ rest)⟩, 1) from rfl)
                    (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec σ, .Rt, .V :: .P1 :: (w ++ rest)⟩
                      = some (⟨.W :: cdec σ, .Rt, .P1 :: (w ++ rest)⟩, 2) from rfl))))
              · intro _
                simp only [paid_false, tstep_X]
                rw [cdec_cval hst1.consW hWv]
                omega
      obtain ⟨p₁, phys₁, k₁, hrun₁, hst₁, hpaid₁, hcv₁⟩ := key
      have hp₁ : p₁ = false → 1 ≤ cval phys₁ := by
        intro hpf
        have := hcv₁ hpf
        omega
      have hcl₂ : 0 ≤ rrun w (cval (paid p₁ phys₁)) := by
        rw [hpaid₁]
        have hpst : CStack (paid p σ) := by
          cases p with
          | true => simpa using hst
          | false => simpa using cdec_CStack_all hst
        rw [tstep_cval hb hpst hcl1]
        simpa using hcl
      obtain ⟨p', phys, k, hrun, hstp, hpaidp, hcvp⟩ :=
        ih hw' p₁ phys₁ hst₁ hp₁ hcl₂ rest
      refine ⟨p', phys, k₁ + k, ?_, hstp, ?_, ?_⟩
      · simpa using hrun₁.trans hrun
      · rw [hpaidp, hpaid₁, tfold_cons]
      · intro hpf
        rw [hcvp hpf, hpaid₁, tfold_cons]

end BB25.Prefix
