/-
# The early cases of the `0RB` branch: the machine

Sections 8.2–8.4 of the submitted argument, reduced to two statements about
*words*.

When the counter under the `01` is spent before the pop, the stack overflows
and deposits its decoded word `P(σ)` in front of the residual digit `d` and the
generated word `w`.  Two things can happen.

* **The early reset is clean** (Section 8.3).  The word `P(σ) d` is re-parsed
  over the bare left end, giving the stack `t`; the two pending digits then
  cancel into one zero bit and the head reads `w` in the *counter* phase, which
  re-emits `w` into the decoder and multiplies `counter + 1` by `2^h`.  The
  right end then drains the whole counter, so the reset word the machine
  finally rebuilds is
  ```
    P(t) Y w chi(2^(h+1) (v(t)+1)) V
  ```
  (`wordCD`, the word (10) of the document, since
  `chi (2^(h+1) m) = X^(h+1) chi m`).  That this word is positive and ready is
  Lemma C.

* **The early reset is dirty** (Section 8.4).  Only the residual `11` block can
  fail, and only over a decoded value of `0` or `1`.  Then the pop leaves an
  exhausted stack `q`, the pending decrement fails as well and the machine
  overflows once more, so the reset word is `P(q) Y w` — and the scan of `w`
  alone settles it (Lemma A).

The same drain lemma also covers the exceptional case 8.2, where the word read
in the counter phase is the balanced `Y V` rather than a generated word.
-/
import RequestProject.BB25.Prefix.RB.Clock

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The reset of a word over the bare left end -/

/-- **The reset of a clean word at the bare left end.**  The pending `2>`
re-parses the word; the right end then turns the head straight into a `0RB`
checkpoint. -/
theorem sret0_reset_left {W u : List RB} (hw : Digs W) (hend : W = u ++ [.V])
    (hpos : 1 ≤ rrun W 0) (hready : Ready (TW W)) :
    SRet b4 ⟨[LB.L], .Rt, .P2 :: (W ++ [.R])⟩ := by
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hpos' : 1 ≤ rrun W (cval ([LB.L] : List LB)) := by rw [hL]; simpa using hpos
  exact sret0_reset_end CStack.base adm_L good_L strict_L hw hend hpos' hready

/-! ## The counter phase and the drain -/

/-- **The counter phase over a stack, followed by the drain.**  The head reads
the colored Dyck word `v` in the counter phase above `.Z :: t`, the right end
drains the counter it has built, and the overflow rebuilds the reset word
`wordCD t v h`. -/
theorem sret0_counter_drain {t : List LB} (hst : CStack t) {v : List RB} {h : ℕ}
    (hd : DyckRun 0 v h) (hpos : 1 ≤ rrun (wordCD t v h) 0)
    (hready : Ready (TW (wordCD t v h))) :
    SRet b4 ⟨.Z :: t, .Rt, v ++ [.R]⟩ := by
  -- the counter phase
  have hA : cval (.Z :: t) + 1 = 2 ^ 0 * ((2 * cval t + 1) + 1) := by
    simp only [cval_Z, pow_zero, one_mul]
  obtain ⟨hst1, hcv1, hpd1, k1, hrun1⟩ :=
    cfold_props_gen (b4 := b4) (2 * cval t + 1) hd hst.consZ hA [.R]
  set π : List LB := cfold (.Z :: t) v with hπ
  have hcvπ : cval π + 1 = 2 ^ (h + 1) * (cval t + 1) := by
    rw [hcv1, pow_succ]
    ring
  -- the drain
  obtain ⟨σ', k2, hst2, hv2, hw2, hrun2⟩ :=
    drain_plain (b4 := b4) [LB.L] (cval π) π (le_refl _) hst1
  rw [rep_L_self hst1] at hrun2
  have hword : pdec σ' ++ [RB.V] = wordCD t v h := by
    rw [hw2, hpd1, dword_eq_chi, hcvπ, wordCD, pdec_Z]
  refine SRet.of_run (hrun1.trans hrun2) ?_
  refine SRet.of_step (show bstep b4 ⟨[LB.L], .Lt, pdec σ' ++ [RB.V, .R]⟩
    = some (⟨[LB.L], .Rt, .P2 :: (pdec σ' ++ [RB.V, .R])⟩, 4) from rfl) ?_
  have hsplit : pdec σ' ++ [RB.V, RB.R] = (pdec σ' ++ [RB.V]) ++ [RB.R] := by simp
  rw [hsplit, hword]
  exact sret0_reset_left (digs_wordCD hd.digs) rfl hpos hready

/-! ## The two pending digits -/

/-- The pending digit left by an early reset, together with the displayed `2>`,
pays the outstanding decrement and pushes one bit. -/
theorem brun_pd_push {p : Bool} {phys : List LB} (hst : CStack phys)
    (hp : p = false → 1 ≤ cval phys) (rest : List RB) :
    ∃ k, BRun b4 ⟨phys, .Rt, pd p :: .P2 :: rest⟩ ⟨.Z :: paid p phys, .Rt, rest⟩ k := by
  cases p with
  | true =>
      refine ⟨0 + 2, ?_⟩
      exact BRun.head (show bstep b4 ⟨phys, .Rt, .P2 :: .P2 :: rest⟩
          = some (⟨phys, .Rt, .Y :: rest⟩, 0) from rfl)
        (BRun.of_step (show bstep b4 ⟨phys, .Rt, RB.Y :: rest⟩
          = some (⟨.Z :: phys, .Rt, rest⟩, 2) from rfl))
  | false =>
      obtain ⟨k, hrun⟩ := brun_cdec_of (b4 := b4) hst (hp rfl) (.Y :: rest)
      refine ⟨0 + (1 + (k + 2)), ?_⟩
      exact BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .P2 :: rest⟩
          = some (⟨phys, .Rt, .U :: rest⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: rest⟩
            = some (⟨phys, .Lt, .Y :: rest⟩, 1) from rfl)
          (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec phys, .Rt, RB.Y :: rest⟩
            = some (⟨.Z :: cdec phys, .Rt, rest⟩, 2) from rfl))))

/-! ## The early overflow -/

/-- **The early overflow.**  The head sweeps left into an exhausted counter
with one residual digit, the generated word and the bare right end in front of
it. -/
theorem sret0_overflow_gen {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    (hstr : Strict σ) (hv : cval σ = 0) {d : RB} (hd : d = RB.X ∨ d = RB.V)
    (hdV : d = RB.V → pdec σ ≠ []) {w : List RB} {h : ℕ} (hgen : Gen w h) :
    SRet b4 ⟨σ, .Lt, d :: .P2 :: (w ++ [.R])⟩ := by
  have hB0 : 0 ≤ bval σ := by
    have h := hg.head
    rw [hv] at h
    simpa using h
  have hru : rrun (pdec σ) 0 = bval σ := (bval_eq_rrun σ).symm
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hst hv (d :: .P2 :: (w ++ [.R]))
  rw [ofw_eq_pdec hst hv] at hr0
  have hdig : Dig d := by
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hwd : Digs (pdec σ ++ [d]) := (pdec_digs σ).append (by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact hdig)
  by_cases hclean : 0 ≤ rstep d (bval σ)
  · -- 8.3: the early reset is clean
    have hune : pdec σ ≠ [] := by
      rcases hd with rfl | rfl
      · intro h0
        have hb0 : bval σ = 0 := by rw [← hru, h0]; rfl
        rw [hb0] at hclean
        simp at hclean
      · exact hdV rfl
    have hcl : 0 ≤ rrun (pdec σ ++ [d]) 0 := by
      rw [rrun_append, hru]
      exact hclean
    have happ : pdec σ ++ (d :: .P2 :: (w ++ [.R]))
        = (pdec σ ++ [d]) ++ (.P2 :: (w ++ [.R])) := by simp
    rw [happ] at hr0
    refine SRet.of_run (hr0.trans (BRun.of_step
      (show bstep b4 ⟨[LB.L], .Lt, (pdec σ ++ [d]) ++ (.P2 :: (w ++ [.R]))⟩
        = some (⟨[LB.L], .Rt, .P2 :: ((pdec σ ++ [d]) ++ (.P2 :: (w ++ [.R])))⟩, 4)
        from rfl))) ?_
    obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
      brun_paid (b4 := b4) (pdec σ ++ [d]) hwd true [LB.L] CStack.base (by simp)
        (by simpa [hL] using hcl) (.P2 :: (w ++ [.R]))
    obtain ⟨hstt, hadmt, hgt, hcvt, -, -⟩ :=
      tfold_props (pdec σ ++ [d]) hwd (σ := [LB.L]) CStack.base adm_L good_L
        (by simpa [hL] using hcl)
    set t : List LB := tfold [LB.L] (pdec σ ++ [d]) with ht
    have hpaid' : paid p' phys = t := by simpa using hpaid
    refine SRet.of_run hrun ?_
    obtain ⟨k₂, hrun₂⟩ := brun_pd_push (b4 := b4) hstp (by
      intro hpf
      have := hcvp hpf
      omega) (w ++ [.R])
    rw [hpaid'] at hrun₂
    refine SRet.of_run hrun₂ ?_
    exact sret0_counter_drain hstt hgen.dyck
      (lemmaC hgt (slack_early hadm hstr hB0 hd hclean hune) hgen).1
      (lemmaC hgt (slack_early hadm hstr hB0 hd hclean hune) hgen).2
  · -- 8.4: the early reset is dirty
    have hdX : d = RB.X := by
      rcases hd with h | h
      · exact h
      · rw [h] at hclean
        exact absurd (by simpa using (by omega : (0:ℤ) ≤ 2 * bval σ)) hclean
    subst hdX
    have hB1 : bval σ ≤ 1 := by
      simp only [rstep_X] at hclean
      omega
    obtain ⟨v, hv'⟩ := gen_start_Y hgen
    rcases eq_or_ne (pdec σ) [] with hu0 | hune
    · -- the stack is empty: the head falls into the left-end spinout
      rw [hu0] at hr0
      simp only [List.nil_append] at hr0
      rw [hv'] at hr0 ⊢
      refine Or.inr ⟨_, _, ⟨v ++ [RB.R], rfl, ?_⟩, hr0⟩
      have hfv := fgc_digs hgen.digs
      rw [hv'] at hfv
      simp only [fgc_cons, fgc_append] at hfv ⊢
      simp at hfv ⊢
      omega
    · -- reset the decoded word, consume the `11` block and overflow once more
      have hwu : Digs (pdec σ) := pdec_digs σ
      have hdu : DyckPre (pdec σ) := pdec_dyck hadm
      have hclu : 0 ≤ rrun (pdec σ) (cval (paid true [LB.L])) := by
        simp only [paid_true, hL, Nat.cast_zero, hru]
        exact hB0
      obtain ⟨p₁, phys₁, k₁, hrun₁, hst₁, hpaid₁, hcv₁⟩ :=
        brun_paid (b4 := b4) (pdec σ) hwu true [LB.L] CStack.base (by simp) hclu
          (.X :: .P2 :: (w ++ [.R]))
      obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, -⟩ :=
        tfold_props (pdec σ) hwu (σ := [LB.L]) CStack.base adm_L good_L (by
          simp only [hL, Nat.cast_zero, hru]
          exact hB0)
      set t₀ : List LB := tfold [LB.L] (pdec σ) with ht₀
      have hpaid₁' : paid p₁ phys₁ = t₀ := by simpa using hpaid₁
      have hcvtB : (cval t₀ : ℤ) = bval σ := by
        rw [hcvt, hL, Nat.cast_zero, hru]
      have hbvt' : bval t₀ = trun (pdec σ) 0 0 := by
        rw [hbvt, hL, Nat.cast_zero]
        rfl
      obtain ⟨k₂, hrun₂⟩ : ∃ k, BRun b4 ⟨phys₁, .Rt, pd p₁ :: (RB.X :: .P2 :: (w ++ [.R]))⟩
          ⟨.W :: t₀, .Rt, .P1 :: .P2 :: (w ++ [.R])⟩ k := by
        cases p₁ with
        | true =>
            have hpe : phys₁ = t₀ := by simpa using hpaid₁'
            subst hpe
            exact ⟨0 + 2, BRun.head
              (show bstep b4 ⟨t₀, .Rt, .P2 :: RB.X :: .P2 :: (w ++ [.R])⟩
                = some (⟨t₀, .Rt, .V :: .P1 :: .P2 :: (w ++ [.R])⟩, 0) from rfl)
              (BRun.of_step (show bstep b4 ⟨t₀, .Rt, .V :: .P1 :: .P2 :: (w ++ [.R])⟩
                = some (⟨.W :: t₀, .Rt, .P1 :: .P2 :: (w ++ [.R])⟩, 2) from rfl))⟩
        | false =>
            have hcvp : cval phys₁ = cval t₀ + 1 := by simpa using hcv₁ rfl
            have hcd : cdec phys₁ = t₀ := by simpa using hpaid₁'
            obtain ⟨k, hrunk⟩ :=
              brun_cdec_of (b4 := b4) hst₁ (by omega) (.V :: .P1 :: .P2 :: (w ++ [.R]))
            rw [hcd] at hrunk
            exact ⟨0 + (1 + (k + 2)), BRun.head
              (show bstep b4 ⟨phys₁, .Rt, .P1 :: RB.X :: .P2 :: (w ++ [.R])⟩
                = some (⟨phys₁, .Rt, .X :: .P1 :: .P2 :: (w ++ [.R])⟩, 0) from rfl)
              (BRun.head (show bstep b4 ⟨phys₁, .Rt, RB.X :: .P1 :: .P2 :: (w ++ [.R])⟩
                  = some (⟨phys₁, .Lt, .V :: .P1 :: .P2 :: (w ++ [.R])⟩, 1) from rfl)
                (hrunk.trans (BRun.of_step
                  (show bstep b4 ⟨t₀, .Rt, .V :: .P1 :: .P2 :: (w ++ [.R])⟩
                    = some (⟨.W :: t₀, .Rt, .P1 :: .P2 :: (w ++ [.R])⟩, 2) from rfl))))⟩
      have hcvW : cval (.W :: t₀) = 0 := by
        simp only [cval_W]
        omega
      have hbW : 0 ≤ bval (.W :: t₀) := by
        rcases (show cval t₀ = 0 ∨ cval t₀ = 1 by omega) with h0 | h1
        · have hbt : 2 ≤ bval t₀ := by
            rw [hbvt']
            exact trun_ge_two hwu hdu hune (by rw [hru]; omega)
          simp only [bval_W, h0]
          norm_num
          omega
        · have hbt : (1 : ℤ) ≤ bval t₀ := by
            have := hgt.head
            omega
          simp only [bval_W, h1]
          norm_num
          omega
      have hstW : CStack (.W :: t₀) := hstt.consW
      obtain ⟨k₃, hrun₃⟩ := brun_overflow_of (b4 := b4) hstW hcvW (.Y :: (w ++ [.R]))
      rw [ofw_eq_pdec hstW hcvW] at hrun₃
      -- the final reset word
      set q : List LB := .W :: t₀ with hq
      set W₄ : List RB := pdec q ++ [RB.Y] ++ w with hW₄
      have hdigs₄ : Digs W₄ := ((pdec_digs q).append (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact Or.inl rfl)).append hgen.digs
      have hbq : rrun (pdec q) 0 = bval q := (bval_eq_rrun q).symm
      have hbase : rrun (pdec q ++ [RB.Y]) 0 = 2 * bval q + 1 := by
        rw [rrun_append, hbq]
        simp
      -- positivity
      have hposq : 1 ≤ rrun (pdec q ++ [RB.Y]) 0 := by rw [hbase]; omega
      have hpos₄ : 1 ≤ rrun W₄ 0 := by
        rw [hW₄, rrun_append]
        exact gen_rrun_pos hgen (by omega) (Or.inr (by omega))
      -- readiness
      have hclq : 0 ≤ rrun (pdec q ++ [RB.Y]) (cval ([LB.L] : List LB)) := by
        rw [hL]
        simpa using by omega
      obtain ⟨hstp, hadmp, hgp, hcvp, -, -⟩ :=
        tfold_props (pdec q ++ [RB.Y]) ((pdec_digs q).append (by
          intro c hc
          simp only [List.mem_singleton] at hc
          subst hc
          exact Or.inl rfl)) (σ := [LB.L]) CStack.base adm_L good_L hclq
      set ρ : List LB := tfold [LB.L] (pdec q ++ [RB.Y]) with hρ
      have hcvρ : (cval ρ : ℤ) = rrun (pdec q ++ [RB.Y]) 0 := by
        rw [hρ, hcvp, hL]
        simp
      have hready₄ : Ready (TW W₄) := by
        have hfold : TW W₄ = tfold ρ w := by
          rw [hW₄, hρ, TW, tfold_append]
        rw [hfold]
        refine ready_tfold_of_stops hgen.digs hstp hadmp hgp ?_ ?_
        · rw [hcvρ]
          have := gen_rrun_pos hgen (a := rrun (pdec q ++ [RB.Y]) 0) (by omega)
            (Or.inr (by omega))
          omega
        · exact gen_scan_stops hgen (by rw [hcvρ]; omega)
      obtain ⟨uu, huu⟩ := gen_end_V hgen
      have hend₄ : W₄ = (pdec q ++ [RB.Y] ++ uu) ++ [RB.V] := by
        rw [hW₄, huu]
        simp
      -- the machine
      refine SRet.of_run (hr0.trans (BRun.of_step (show bstep b4
          ⟨[LB.L], .Lt, pdec σ ++ (RB.X :: .P2 :: (w ++ [.R]))⟩
          = some (⟨[LB.L], .Rt, .P2 :: (pdec σ ++ (RB.X :: .P2 :: (w ++ [.R])))⟩, 4)
          from rfl))) ?_
      refine SRet.of_run hrun₁ (SRet.of_run hrun₂ ?_)
      refine SRet.of_run (BRun.head (show bstep b4 ⟨q, .Rt, .P1 :: .P2 :: (w ++ [.R])⟩
          = some (⟨q, .Rt, .U :: (w ++ [.R])⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨q, .Rt, .U :: (w ++ [.R])⟩
            = some (⟨q, .Lt, .Y :: (w ++ [.R])⟩, 1) from rfl) hrun₃)) ?_
      refine SRet.of_run (BRun.of_step (show bstep b4
        ⟨[LB.L], .Lt, pdec q ++ (RB.Y :: (w ++ [.R]))⟩
        = some (⟨[LB.L], .Rt, .P2 :: (pdec q ++ (RB.Y :: (w ++ [.R])))⟩, 4) from rfl)) ?_
      have hsplit : pdec q ++ (RB.Y :: (w ++ [RB.R])) = W₄ ++ [RB.R] := by
        rw [hW₄]
        simp
      rw [hsplit]
      exact sret0_reset_left hdigs₄ hend₄ hpos₄ hready₄

end BB25.Prefix
