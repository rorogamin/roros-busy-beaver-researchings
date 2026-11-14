/-
# `1LA` never halts

This file closes the `1LA` member.  `LA.lean` reduced its non-halting to
`ZReady`: the statement that the member-independent `01` branch of the `<B1`
sweep returns to a checkpoint whose own scan succeeds.  The four previous files
supply the two halves of that statement —

* `Exact.lean`: the checkpoint the branch reaches is the paid stack of an
  explicit reset word;
* `Direct.lean`: that word is ready.

What is left, and is done here, is the case distinction of the branch itself
(Section 7 of the submitted argument): a counter of at least two drains as
above, while an exhausted counter overflows early.  A clean early reset ends in
the `22`-run of `returns_Yrun`, whose checkpoint has the literal shape
`X Z …`, hence is ready for free; the exceptional early reset spends one more
overflow and then lands in a drain with a run of at least three `22` blocks,
which is again `ready_drain_word`.
-/
import RequestProject.BB25.Prefix.LA.Exact

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Returns with an explicit spinout

`SRet b4 c`: from `c` the block simulator runs to a ready checkpoint, or to the
left-end spinout `L <A 11 2> 22 …`.  Unlike `RReturns`, both alternatives are
explicit block runs, so the statement also transfers to the sibling machine
(`Sibling/`).  `zready` is derived from `zreadyS` at the end of the file. -/

/-- The left-end spinout configuration reached by an exhausted counter. -/
def SpinCfg (c : BCfg) : Prop :=
  ∃ rest : List RB, c = ⟨[.L], .Lt, .X :: .P2 :: .Y :: rest⟩ ∧ fgc rest = 0

/-- A run to a ready checkpoint or to the left-end spinout. -/
def SRet (b4 : Option (Sym × Dir × St)) (c : BCfg) : Prop :=
  (∃ (s : List LB) (k : ℕ), ReadyCP s ∧ BRun b4 c (cpCfg s) k) ∨
    (∃ (c' : BCfg) (k : ℕ), SpinCfg c' ∧ BRun b4 c c' k)

theorem SRet.of_run {c c' : BCfg} {k : ℕ} (hr : BRun b4 c c' k) (h : SRet b4 c') : SRet b4 c := by
  rcases h with ⟨s, k', hs, hrun⟩ | ⟨c'', k', hs, hrun⟩
  · exact Or.inl ⟨s, k + k', hs, hr.trans hrun⟩
  · exact Or.inr ⟨c'', k + k', hs, hr.trans hrun⟩

theorem SRet.of_step {c c' : BCfg} {k : ℕ} (hs : bstep b4 c = some (c', k)) (h : SRet b4 c') :
    SRet b4 c :=
  SRet.of_run (BRun.of_step hs) h

theorem SRet.cp {s : List LB} (h : ReadyCP s) : SRet b4 (cpCfg s) :=
  Or.inl ⟨s, 0, h, BRun.refl _⟩

/-- The spinout never halts. -/
theorem SpinCfg.not_halts {c : BCfg} (h : SpinCfg c) : ¬ Halts (M b4) c.den := by
  obtain ⟨rest, rfl, -⟩ := h
  exact not_halts_overflow_left rest

theorem SRet.rreturns {c : BCfg} (h : SRet b4 c) : RReturns b4 c := by
  rcases h with h | ⟨c', k, hs, hrun⟩
  · exact Or.inl h
  · exact Or.inr (hrun.not_halts hs.not_halts)

/-! ## The drain of a good stack -/

/-- **A pending `2>` in front of a run of at least two `22` blocks returns to a
ready checkpoint.** -/
theorem sret_tail {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    {r : ℕ} (hr : 2 ≤ r) :
    SRet b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  obtain ⟨hcp, hstr, k, hrun⟩ :=
    exact_tail (b4 := b4) hst hadm (tail_bound_of_good hg) (show 1 ≤ r by omega)
  exact Or.inl ⟨_, k, ⟨hcp, ready_drain_word hg hr, hstr⟩, hrun⟩

/-! ## The head swallowing a run of `22` blocks -/

/-- **A run of at least two `22` blocks in front of the terminal `1` returns to
a ready checkpoint**: the checkpoint it reaches begins with a zero bit over a
one bit, so its scan stops at once. -/
theorem sret_Yrun {π : List LB} (hst : CStack π) (hadm : Adm π) (hg : Good π)
    (hstr : Strict π) {q : ℕ} (hq : 2 ≤ q) :
    SRet b4 ⟨π, .Rt, List.replicate q .Y ++ [.R1]⟩ := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  set ρ : List LB := List.replicate (q' + 2) .Z ++ π with hρ
  have hstρ : CStack ρ := CStack_Zrun _ hst
  have hadmρ : Adm ρ := Adm_Zrun _ hadm
  have hgρ : Good ρ := Good_Zrun _ hg
  have hcρ : cval ρ = 2 ^ (q' + 2) * (cval π + 1) - 1 := cval_Zrun _ _
  have hmul : 4 ≤ 2 ^ (q' + 2) * (cval π + 1) := by
    have hpow : (4 : ℕ) ≤ 2 ^ (q' + 2) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (q' + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans hpow (Nat.le_mul_of_pos_right _ (by omega))
  have h1 : 1 ≤ cval ρ := by omega
  have hrun1 : BRun b4 ⟨π, .Rt, List.replicate (q' + 2) .Y ++ [.R1]⟩ ⟨ρ, .Rt, [.R1]⟩
      (2 * (q' + 2)) := brun_Yrun _ π [.R1]
  have hs1 : bstep b4 ⟨ρ, .Rt, [RB.R1]⟩ = some (⟨ρ, .Lt, [.R2]⟩, 1) := rfl
  obtain ⟨k, hrk⟩ := brun_cdec_of (b4 := b4) hstρ h1 [.R2]
  have hs2 : bstep b4 ⟨cdec ρ, .Rt, [RB.R2]⟩ = some (⟨cdec ρ, .Bt, [.Y, .R1]⟩, 11) := rfl
  -- the checkpoint, and its shape
  have hshape : cdec ρ = .X :: (.Z :: (List.replicate q' .Z ++ π)) := by
    rw [hρ, show List.replicate (q' + 2) LB.Z = LB.Z :: LB.Z :: List.replicate q' LB.Z by
      rw [List.replicate_succ, List.replicate_succ]]
    simp [cdec_Z]
  refine Or.inl ⟨cdec ρ, 2 * (q' + 2) + (1 + (k + 11)), ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact cdec_CStack_all hstρ
  · exact Adm.cdec hstρ hadmρ h1
  · exact Good.cdec hstρ hgρ h1
  · rw [cdec_cval hstρ h1]
    omega
  · exact ⟨_, hshape⟩
  · rw [hshape]
    exact Ready.bit (Ready.zero _)
  · exact (Strict_Zrun (q' + 2) hadm hstr).cdec hstρ h1
  · exact hrun1.trans (BRun.head hs1 (hrk.trans (BRun.of_step hs2)))

/-! ## Resetting a deposited word -/

/-- **The reset of a clean word followed by a pending digit and the tail.** -/
theorem sret_reset_P2 {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0)
    {r : ℕ} (hr : 1 ≤ r) :
    SRet b4 ⟨[LB.L], .Rt, .P2 :: (w ++ (.P2 :: (List.replicate r .Y ++ [.R1])))⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hcl' : 0 ≤ rrun w (cval (paid true [LB.L])) := by
    simpa [hL] using hcl
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hw true [LB.L] CStack.base (by simp) hcl' (.P2 :: tail)
  obtain ⟨hstπ, hadmπ, hgπ, hcvπ, -, -⟩ :=
    tfold_props w hw (σ := [LB.L]) CStack.base adm_L good_L (by simpa [hL] using hcl)
  set π : List LB := tfold [LB.L] w with hπ
  have hpaid' : paid p' phys = π := by simpa using hpaid
  have hY : RB.Y :: tail = List.replicate (r + 1) RB.Y ++ [RB.R1] := by
    rw [htail, List.replicate_succ, List.cons_append]
  have hfin : SRet b4 ⟨π, .Rt, RB.Y :: tail⟩ := by
    rw [hY]
    exact sret_Yrun hstπ hadmπ hgπ (strict_TW hw hcl) (by omega)
  refine SRet.of_run (c' := ⟨phys, .Rt, pd p' :: (.P2 :: tail)⟩) hrun ?_
  cases p' with
  | true =>
      have hpe : phys = π := by simpa using hpaid'
      subst hpe
      exact SRet.of_run (BRun.of_step (show bstep b4 ⟨π, .Rt, .P2 :: .P2 :: tail⟩
        = some (⟨π, .Rt, .Y :: tail⟩, 0) from rfl)) hfin
  | false =>
      have hcv : cval phys = cval π + 1 := by simpa using hcvp rfl
      have hcd : cdec phys = π := by simpa using hpaid'
      obtain ⟨k', hrun'⟩ := brun_cdec_of (b4 := b4) hstp (by omega) (.Y :: tail)
      rw [hcd] at hrun'
      refine SRet.of_run (BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .P2 :: tail⟩
          = some (⟨phys, .Rt, .U :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: tail⟩
            = some (⟨phys, .Lt, .Y :: tail⟩, 1) from rfl) hrun')) hfin

/-- **The reset of a clean word followed by a run of at least three `22`
blocks.** -/
theorem sret_reset_Yrun {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0)
    {q : ℕ} (hq : 3 ≤ q) :
    SRet b4 ⟨[LB.L], .Rt, .P2 :: (w ++ (List.replicate q .Y ++ [.R1]))⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set tail : List RB := List.replicate m RB.Y ++ [RB.R1] with htail
  have hsplit : List.replicate (m + 1) RB.Y ++ [RB.R1] = RB.Y :: tail := by
    rw [htail, List.replicate_succ, List.cons_append]
  rw [hsplit]
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hcl' : 0 ≤ rrun w (cval (paid true [LB.L])) := by
    simpa [hL] using hcl
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hw true [LB.L] CStack.base (by simp) hcl' (.Y :: tail)
  obtain ⟨hstπ, hadmπ, hgπ, -, -, -⟩ :=
    tfold_props w hw (σ := [LB.L]) CStack.base adm_L good_L (by simpa [hL] using hcl)
  set π : List LB := tfold [LB.L] w with hπ
  have hpaid' : paid p' phys = π := by simpa using hpaid
  refine SRet.of_run (c' := ⟨phys, .Rt, pd p' :: (.Y :: tail)⟩) hrun ?_
  cases p' with
  | true =>
      have hpe : phys = π := by simpa using hpaid'
      subst hpe
      rw [show RB.Y :: tail = List.replicate (m + 1) RB.Y ++ [RB.R1] from hsplit.symm]
      exact sret_tail hstπ hadmπ hgπ (by omega)
  | false =>
      have hcv : cval phys = cval π + 1 := by simpa using hcvp rfl
      have hcd : cdec phys = π := by simpa using hpaid'
      obtain ⟨k', hrun'⟩ := brun_cdec_of (b4 := b4) hstp (by omega)
        (.Y :: .P2 :: (List.replicate m RB.Y ++ [RB.R1]))
      rw [hcd] at hrun'
      refine SRet.of_run (BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .Y :: tail⟩
          = some (⟨phys, .Rt, .U :: .P2 :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: .P2 :: tail⟩
            = some (⟨phys, .Lt, .Y :: .P2 :: tail⟩, 1) from rfl)
          (hrun'.trans (BRun.of_step (show bstep b4 ⟨π, .Rt, .Y :: .P2 :: tail⟩
            = some (⟨.Z :: π, .Rt, .P2 :: tail⟩, 2) from rfl))))) ?_
      rw [htail]
      exact sret_tail hstπ.consZ (adm_consZ hadmπ) (good_consZ hgπ) (by omega)

/-! ## The early overflow -/

/-- **The early overflow returns to a ready checkpoint.**  The head is about to
sweep left into an exhausted counter, with one residual digit and a run of at
least two `22` blocks in front of it. -/
theorem sret_overflow {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hB0 : 0 ≤ bval σ)
    (hv : cval σ = 0) {d : RB} (hd : d = RB.X ∨ d = RB.V) {r : ℕ} (hr : 2 ≤ r) :
    SRet b4 ⟨σ, .Lt, d :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have hru : rrun (pdec σ) 0 = bval σ := (bval_eq_rrun σ).symm
  obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hst hv (d :: .P2 :: tail)
  rw [ofw_eq_pdec hst hv] at hr0
  by_cases hclean : 0 ≤ rstep d (bval σ)
  · -- the whole reset word `pdec σ ++ [d]` is clean
    have hdig : Dig d := by
      rcases hd with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
    have hw : Digs (pdec σ ++ [d]) := (pdec_digs σ).append (by
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact hdig)
    have hcl : 0 ≤ rrun (pdec σ ++ [d]) 0 := by
      rw [rrun_append, hru]
      exact hclean
    have happ : pdec σ ++ (d :: .P2 :: tail) = (pdec σ ++ [d]) ++ (.P2 :: tail) := by
      simp
    rw [happ] at hr0
    refine SRet.of_run (hr0.trans (BRun.of_step
      (show bstep b4 ⟨[LB.L], .Lt, (pdec σ ++ [d]) ++ (.P2 :: tail)⟩
        = some (⟨[LB.L], .Rt, .P2 :: ((pdec σ ++ [d]) ++ (.P2 :: tail))⟩, 4) from rfl))) ?_
    rw [htail]
    exact sret_reset_P2 hw hcl (by omega)
  · -- the exceptional case: the residual digit is a `11` block and the decoded
    -- value of the stack is `0` or `1`
    have hdX : d = RB.X := by
      rcases hd with h | h
      · exact h
      · rw [h] at hclean
        exact absurd (by simpa using (by omega : (0:ℤ) ≤ 2 * bval σ)) hclean
    subst hdX
    have hB1 : bval σ ≤ 1 := by
      simp only [rstep_X] at hclean
      omega
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hsplit : tail = RB.Y :: (List.replicate m RB.Y ++ [RB.R1]) := by
      rw [htail, List.replicate_succ, List.cons_append]
    rcases eq_or_ne (pdec σ) [] with hu0 | hune
    · -- the stack is empty: the head falls into the left-end spinout
      rw [hu0] at hr0
      simp only [List.nil_append] at hr0
      rw [hsplit] at hr0
      refine Or.inr ⟨_, _, ⟨List.replicate m RB.Y ++ [RB.R1], rfl, ?_⟩, hr0⟩
      simp [fgc_append, fgc_replicate]
    · -- reset the decoded word, consume the `11` block and overflow once more
      have hwu : Digs (pdec σ) := pdec_digs σ
      have hdu : DyckPre (pdec σ) := pdec_dyck hadm
      have hL : cval ([LB.L] : List LB) = 0 := rfl
      have hclu : 0 ≤ rrun (pdec σ) (cval (paid true [LB.L])) := by
        simp only [paid_true, hL, Nat.cast_zero, hru]
        exact hB0
      obtain ⟨p₁, phys₁, k₁, hrun₁, hst₁, hpaid₁, hcv₁⟩ :=
        brun_paid (b4 := b4) (pdec σ) hwu true [LB.L] CStack.base (by simp) hclu
          (.X :: .P2 :: tail)
      obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, hcnt⟩ :=
        tfold_props (pdec σ) hwu (σ := [LB.L]) CStack.base adm_L good_L (by
          simp only [hL, Nat.cast_zero, hru]
          exact hB0)
      set t : List LB := tfold [LB.L] (pdec σ) with ht
      have hpaid₁' : paid p₁ phys₁ = t := by simpa using hpaid₁
      have hcvtB : (cval t : ℤ) = bval σ := by
        rw [hcvt, hL, Nat.cast_zero, hru]
      have hbvt' : bval t = trun (pdec σ) 0 0 := by
        rw [hbvt, hL, Nat.cast_zero]
        rfl
      obtain ⟨k₂, hrun₂⟩ : ∃ k, BRun b4 ⟨phys₁, .Rt, pd p₁ :: (RB.X :: .P2 :: tail)⟩
          ⟨.W :: t, .Rt, .P1 :: .P2 :: tail⟩ k := by
        cases p₁ with
        | true =>
            have hpe : phys₁ = t := by simpa using hpaid₁'
            subst hpe
            exact ⟨0 + 2, BRun.head
              (show bstep b4 ⟨t, .Rt, .P2 :: RB.X :: .P2 :: tail⟩
                = some (⟨t, .Rt, .V :: .P1 :: .P2 :: tail⟩, 0) from rfl)
              (BRun.of_step (show bstep b4 ⟨t, .Rt, .V :: .P1 :: .P2 :: tail⟩
                = some (⟨.W :: t, .Rt, .P1 :: .P2 :: tail⟩, 2) from rfl))⟩
        | false =>
            have hcvp : cval phys₁ = cval t + 1 := by simpa using hcv₁ rfl
            have hcd : cdec phys₁ = t := by simpa using hpaid₁'
            obtain ⟨k, hrunk⟩ :=
              brun_cdec_of (b4 := b4) hst₁ (by omega) (.V :: .P1 :: .P2 :: tail)
            rw [hcd] at hrunk
            exact ⟨0 + (1 + (k + 2)), BRun.head
              (show bstep b4 ⟨phys₁, .Rt, .P1 :: RB.X :: .P2 :: tail⟩
                = some (⟨phys₁, .Rt, .X :: .P1 :: .P2 :: tail⟩, 0) from rfl)
              (BRun.head (show bstep b4 ⟨phys₁, .Rt, RB.X :: .P1 :: .P2 :: tail⟩
                  = some (⟨phys₁, .Lt, .V :: .P1 :: .P2 :: tail⟩, 1) from rfl)
                (hrunk.trans (BRun.of_step
                  (show bstep b4 ⟨t, .Rt, .V :: .P1 :: .P2 :: tail⟩
                    = some (⟨.W :: t, .Rt, .P1 :: .P2 :: tail⟩, 2) from rfl))))⟩
      have hcvW : cval (.W :: t) = 0 := by
        simp only [cval_W]
        omega
      have hbW : 0 ≤ bval (.W :: t) := by
        rcases (show cval t = 0 ∨ cval t = 1 by omega) with h0 | h1
        · have hbt : 2 ≤ bval t := by
            rw [hbvt']
            exact trun_ge_two hwu hdu hune (by rw [hru]; omega)
          simp only [bval_W, h0]
          norm_num
          omega
        · have hbt : (1 : ℤ) ≤ bval t := by
            have := hgt.head
            omega
          simp only [bval_W, h1]
          norm_num
          omega
      have hstW : CStack (.W :: t) := hstt.consW
      obtain ⟨k₃, hrun₃⟩ := brun_overflow_of (b4 := b4) hstW hcvW (.Y :: tail)
      rw [ofw_eq_pdec hstW hcvW] at hrun₃
      have hclW : 0 ≤ rrun (pdec (.W :: t)) 0 := by
        rw [← bval_eq_rrun]
        exact hbW
      have hYtail : RB.Y :: tail = List.replicate (m + 2) RB.Y ++ [RB.R1] := by
        rw [htail, ← List.cons_append, ← List.replicate_succ]
      have hfin : SRet b4 ⟨[LB.L], .Rt, .P2 :: (pdec (.W :: t) ++ (RB.Y :: tail))⟩ := by
        rw [hYtail]
        exact sret_reset_Yrun (pdec_digs _) hclW (by omega)
      refine SRet.of_run (hr0.trans (BRun.of_step (show bstep b4
          ⟨[LB.L], .Lt, pdec σ ++ (RB.X :: .P2 :: tail)⟩
          = some (⟨[LB.L], .Rt, .P2 :: (pdec σ ++ (RB.X :: .P2 :: tail))⟩, 4) from rfl))) ?_
      refine SRet.of_run hrun₁ (SRet.of_run hrun₂ ?_)
      refine SRet.of_run (BRun.head (show bstep b4 ⟨.W :: t, .Rt, .P1 :: .P2 :: tail⟩
          = some (⟨.W :: t, .Rt, .U :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨.W :: t, .Rt, .U :: tail⟩
            = some (⟨.W :: t, .Lt, .Y :: tail⟩, 1) from rfl) hrun₃)) ?_
      exact SRet.of_run (BRun.of_step (show bstep b4
        ⟨[LB.L], .Lt, pdec (.W :: t) ++ (RB.Y :: tail)⟩
        = some (⟨[LB.L], .Rt, .P2 :: (pdec (.W :: t) ++ (RB.Y :: tail))⟩, 4) from rfl)) hfin

/-! ## The `01` branch -/

/-- **The `01` branch before the first pop**: the `01` branch of the `<B1` sweep always returns to a
ready checkpoint. -/
theorem zreadyS : ∀ (c : List LB) (r : ℕ), CStack c → Adm c → Good c → 2 ≤ r →
    SRet b4 ⟨c, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  intro σ r hst hadm hg hr
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
  · have hB0 : 0 ≤ bval σ := by
      have h := hg.head
      rw [h0] at h
      simpa using h
    exact sret_overflow hst hadm hB0 h0 (Or.inl rfl) hr
  · have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
    have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
    have hstd : CStack (cdec σ) := cdec_CStack_all hst
    have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
    have hgd : Good (cdec σ) := Good.cdec hst hg h1
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.X :: .P2 :: tail)
    have hs1 : bstep b4 ⟨cdec σ, .Rt, .X :: .P2 :: tail⟩
        = some (⟨cdec σ, .Lt, .V :: .P2 :: tail⟩, 1) := rfl
    refine SRet.of_run (hr1.trans (BRun.of_step hs1)) ?_
    rcases Nat.eq_zero_or_pos (cval (cdec σ)) with h0' | h1'
    · have hB0 : 0 ≤ bval (cdec σ) := by
        have h := hgd.head
        rw [h0'] at h
        simpa using h
      exact sret_overflow hstd hadmd hB0 h0' (Or.inr rfl) hr
    · have hcv2 : cval (cdec (cdec σ)) = cval (cdec σ) - 1 := cdec_cval hstd h1'
      have hbv2 : bval (cdec (cdec σ)) = bval (cdec σ) := bval_cdec hstd h1'
      have hstd2 : CStack (cdec (cdec σ)) := cdec_CStack_all hstd
      have hadmd2 : Adm (cdec (cdec σ)) := Adm.cdec hstd hadmd h1'
      have hgd2 : Good (cdec (cdec σ)) := Good.cdec hstd hgd h1'
      obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P2 :: tail)
      have hs2 : bstep b4 ⟨cdec (cdec σ), .Rt, .V :: .P2 :: tail⟩
          = some (⟨.W :: cdec (cdec σ), .Rt, .P2 :: tail⟩, 2) := rfl
      refine SRet.of_run (hr2.trans (BRun.of_step hs2)) ?_
      have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched hst hadm h1
      have hgh : (cval σ : ℤ) ≤ bval σ := hg.head
      refine sret_tail hstd2.consW (adm_consW hadmd2 ?_) (good_consW hgd2 ?_) hr
      · rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
        omega
      · rw [hcv2, hcv, hbv2, hbv]
        omega

/-- **`ZReady` holds**: the `01` branch of the `<B1` sweep always returns to a
ready checkpoint. -/
theorem zready : ZReady b4 := fun c r hst hadm hg hr =>
  (zreadyS c r hst hadm hg hr).rreturns

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB1LA` never halts.** -/
theorem not_halts_1LA : ¬ Halts (M b4_1LA) init :=
  not_halts_1LA_of_zready zready

end BB25.Prefix
