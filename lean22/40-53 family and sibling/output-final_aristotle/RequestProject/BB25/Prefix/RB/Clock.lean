/-
# The clock words of the early cases

The two words the early cases of the `0RB` branch rebuild are

```
  (14)   P(t) Y Y V X chi(x+1) V            (Section 7, the exceptional case)
  (10)   P(t) Y w  X^(h+1) chi(x+1) V       (Lemma C, the general case)
```

`x = v(t)` being the counter of the stack the early reset built and `w` the
generated word.  Both are of the shape `wordCD`, and in both the last `V` and
the digits `chi (x+1)` are read the same way; they differ in what sits between
`P(t)` and the digits.

This file proves that the words are positive and ready.  The two ingredients
for the digits are

* `rrun_chi_pos`: reading `chi M` keeps the value above `4M - 3`, hence
  positive;
* `ready_chi` of `LA/Chi.lean`: crossing `chi M` backwards, the debt that
  arrives at its left satisfies `n + 4 ≤ 4M`, and `n + 9 ≤ 2M` when it is odd.
-/
import RequestProject.BB25.Prefix.RB.Phase
import RequestProject.BB25.Prefix.Slack
import RequestProject.BB25.Prefix.RB.Gap

namespace BB25.Prefix

open BB25

/-! ## The value of the drain digits -/

/-- Reading the drain digits from a value above `4M - 3` keeps the value
positive. -/
theorem rrun_chi_pos : ∀ (M : ℕ), 1 ≤ M → ∀ v : ℤ, 4 * (M : ℤ) - 3 ≤ v →
    1 ≤ rrun (chi M) v := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
      intro hM v hv
      rcases lt_or_ge M 2 with hlt | hge
      · obtain rfl : M = 1 := by omega
        rw [chi_of_lt (by omega)]
        simpa using by omega
      · have hM' : 1 ≤ M / 2 := by omega
        have hMlt : M / 2 < M := by omega
        rw [chi_of_le hge, rrun_cons]
        by_cases hpar : M % 2 = 0
        · rw [if_pos hpar, rstep_X]
          refine ih (M / 2) hMlt hM' _ ?_
          have hhalf : 4 * ((M : ℤ) / 2) = 2 * M := by omega
          have hdiv : (2 : ℤ) * M - 2 ≤ v / 2 := by omega
          have hcast : ((M / 2 : ℕ) : ℤ) = (M : ℤ) / 2 := by omega
          rw [hcast]
          omega
        · rw [if_neg hpar, rstep_V]
          refine ih (M / 2) hMlt hM' _ ?_
          have hcast : ((M / 2 : ℕ) : ℤ) = ((M : ℤ) - 1) / 2 := by omega
          rw [hcast]
          omega

/-- The entry bound: a value above `4M - 4` is enough, as soon as `M ≥ 2`. -/
theorem rrun_chi_pos_entry {M : ℕ} (hM : 2 ≤ M) {v : ℤ} (hv : 4 * (M : ℤ) - 4 ≤ v) :
    1 ≤ rrun (chi M) v := by
  have hM' : 1 ≤ M / 2 := by omega
  rw [chi_of_le hM, rrun_cons]
  by_cases hpar : M % 2 = 0
  · rw [if_pos hpar, rstep_X]
    refine rrun_chi_pos (M / 2) hM' _ ?_
    have hcast : ((M / 2 : ℕ) : ℤ) = (M : ℤ) / 2 := by omega
    rw [hcast]
    omega
  · rw [if_neg hpar, rstep_V]
    refine rrun_chi_pos (M / 2) hM' _ ?_
    have hcast : ((M / 2 : ℕ) : ℤ) = ((M : ℤ) - 1) / 2 := by omega
    rw [hcast]
    omega

/-! ## Section 7: the small clock -/

/-- **The small clock of Section 7**: the word the exceptional case rebuilds is
positive and ready. -/
theorem lemma_seven {t : List LB} (hg : Good t) (hx : 1 ≤ cval t) :
    1 ≤ rrun (wordCD t [.Y, .V] 0) 0 ∧ Ready (TW (wordCD t [.Y, .V] 0)) := by
  set M : ℕ := cval t + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hgh : (cval t : ℤ) ≤ bval t := hg.head
  have hchi : chi (2 ^ (0 + 1) * (cval t + 1)) = [RB.X] ++ chi M := by
    have h := chi_two_pow 1 M hM1
    rw [pow_one] at h ⊢
    simpa using h
  have hword : wordCD t [.Y, .V] 0
      = (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X]) ++ chi M ++ [RB.V] := by
    rw [wordCD, hchi]
    simp [List.append_assoc]
  constructor
  · -- positivity
    rw [hword, rrun_append, rrun_append]
    have hval : rrun (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X]) 0
        = 4 * bval t + 2 := by
      rw [rrun_append, rrun_append, rrun_append, rrun_append, ← bval_eq_rrun]
      simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V, rstep_X]
      omega
    rw [hval]
    have hpos : 1 ≤ rrun (chi M) (4 * bval t + 2) := by
      refine rrun_chi_pos M hM1 _ ?_
      have : ((M : ℕ) : ℤ) = (cval t : ℤ) + 1 := by rw [hM]; push_cast; ring
      rw [this]
      omega
    simp only [rrun_cons, rrun_nil, rstep_V]
    omega
  · -- readiness
    rw [hword]
    -- the values along the word
    have hBv : ((cval (TW (pdec t)) : ℕ) : ℤ) = bval t := cval_TW_pdec hg
    have hxB : cval t ≤ cval (TW (pdec t)) := by omega
    have hst0 : CStack (TW (pdec t)) := CStack_TW_pdec hg
    have hst1 : CStack (TW (pdec t ++ [RB.Y])) := CStack_TW_Y hst0
    have hst2 : CStack (TW (pdec t ++ [RB.Y] ++ [RB.Y])) := CStack_TW_Y hst1
    have hst3 : CStack (TW (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V])) := CStack_TW_V hst2
    have hv1 : cval (TW (pdec t ++ [RB.Y])) = 2 * cval (TW (pdec t)) + 1 := cval_TW_Y _
    have hv2 : cval (TW (pdec t ++ [RB.Y] ++ [RB.Y]))
        = 2 * cval (TW (pdec t ++ [RB.Y])) + 1 := cval_TW_Y _
    have hv3 : cval (TW (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V]))
        = 2 * cval (TW (pdec t ++ [RB.Y] ++ [RB.Y])) := cval_TW_V _
    have hv4 : cval (TW (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X]))
        = (cval (TW (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V])) - 2) / 2 :=
      cval_TW_X hst3 (by omega)
    have hstp : CStack (TW (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X])) :=
      CStack_TW_X hst3
    refine ready_V_even
      (u := pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X] ++ chi M) (n := 0) rfl ?_
    simp only [Nat.zero_div, dpow_zero]
    refine ready_chi M hM1 (pdec t ++ [RB.Y] ++ [RB.Y] ++ [RB.V] ++ [RB.X]) hstp
      (by omega) ?_
    intro n hn hoddn
    -- crossing the pop of the clock
    refine ready_X hst3 (by omega) ?_
    -- the zero bit
    refine ready_V_even (u := pdec t ++ [RB.Y] ++ [RB.Y]) (by omega) ?_
    rw [show (2 * n + 4) / 2 = n + 2 by omega]
    by_cases hpar : n % 2 = 0
    · exact ready_Y_even (u := pdec t ++ [RB.Y]) (by omega)
    · refine ready_Y_odd (u := pdec t ++ [RB.Y]) (by omega) ?_
      rw [show (n + 2 - 1) / 2 = (n + 1) / 2 by omega]
      by_cases hpar4 : n % 4 = 3
      · exact ready_Y_even (u := pdec t) (by omega)
      · have hn4 : n % 4 = 1 := by omega
        refine ready_Y_odd (u := pdec t) (by omega) ?_
        rw [show ((n + 1) / 2 - 1) / 2 = (n - 1) / 4 by omega]
        have hodd := hoddn (by omega)
        exact ready_dpow_of_cval hg (by omega)

/-! ## Lemma B -/

/-- A stack with no bits and no pops decodes to the empty word. -/
theorem pdec_eq_nil_of_nbit {s : List LB} (hn : nbit s = 0) (hm : nsh s = 0) : pdec s = [] := by
  cases s with
  | nil => rfl
  | cons b t => cases b <;> first | rfl | simp_all

/-- **Lemma B**, in the form used: the stack an early clean reset builds has
the dyadic slack Lemma C needs. -/
theorem slack_early {σ : List LB} (hadm : Adm σ) (hstr : Strict σ)
    (hB0 : 0 ≤ bval σ) {d : RB} (hd : d = RB.X ∨ d = RB.V)
    (hclean : 0 ≤ rstep d (bval σ)) (hne : pdec σ ≠ []) :
    ∀ k : ℕ, cval (TW (pdec σ ++ [d])) + 1 = 2 ^ k →
      (cval (TW (pdec σ ++ [d])) : ℤ) + 1 ≤ bval (TW (pdec σ ++ [d])) := by
  intro k hk
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hru : rrun (pdec σ) 0 = bval σ := (bval_eq_rrun σ).symm
  have hwu : Digs (pdec σ) := pdec_digs σ
  have hdu : DyckPre (pdec σ) := pdec_dyck hadm
  have hdig : Dig d := by
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hwd : Digs (pdec σ ++ [d]) := hwu.append (digs_singleton hdig)
  have hcl : (0 : ℤ) ≤ rrun (pdec σ ++ [d]) 0 := by
    rw [rrun_append, hru]
    exact hclean
  -- the counter and the decoded value of the stack the reset builds
  obtain ⟨-, -, hgt, hcvt, hbvt, -⟩ :=
    tfold_props (pdec σ ++ [d]) hwd (σ := [LB.L]) CStack.base adm_L good_L
      (by simpa [hL] using hcl)
  have hcv : (cval (TW (pdec σ ++ [d])) : ℤ) = rstep d (bval σ) := by
    rw [TW, hcvt, hL, Nat.cast_zero, rrun_append, hru]
    simp
  have hbv : bval (TW (pdec σ ++ [d]))
      = rstep (qout d (bval σ)) (trun (pdec σ) 0 0) := by
    rw [TW, hbvt, hL, Nat.cast_zero, show bval ([LB.L] : List LB) = 0 from rfl,
      trun_append, hru]
    simp
  -- the decoded value of the source stack is below its transduced value
  obtain ⟨-, -, hgu, hcvu, hbvu, -⟩ :=
    tfold_props (pdec σ) hwu (σ := [LB.L]) CStack.base adm_L good_L
      (by simpa [hL, hru] using hB0)
  have hfB : bval σ ≤ trun (pdec σ) 0 0 := by
    have hgh := hgu.head
    rw [hcvu, hbvu, hL, Nat.cast_zero, show bval ([LB.L] : List LB) = 0 from rfl, hru] at hgh
    exact hgh
  rcases hd with rfl | rfl
  · -- the residual digit is a pop
    simp only [rstep_X] at hcv hclean
    by_cases hodd : bval σ % 2 = 1
    · -- the popped bit is a one bit: the transduced value doubles
      rw [hbv]
      simp only [qout, if_pos hodd, rstep_V]
      omega
    · -- the popped bit is a zero bit: the transduced value halves
      rw [hbv]
      simp only [qout, if_neg hodd, rstep_X]
      -- the counter of the new stack is a power of two, hence so is the old value
      have hcast : (cval (TW (pdec σ ++ [RB.X])) : ℤ) + 1 = ((2 ^ k : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      have hpow : ((2 ^ k : ℕ) : ℤ) = 2 ^ k := by push_cast; ring
      have hpow' : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have hfval : bval σ = 2 ^ (k + 1) := by omega
      -- Lemma B at the level of words
      have hbal : bal (pdec σ) = ((nbit σ - nsh σ : ℕ) : ℤ) := by
        rw [bal_pdec]
        have := hadm.head
        omega
      have hnb : 1 ≤ nbit σ := by
        by_contra hc
        exact hne (pdec_eq_nil_of_nbit (by omega) (by have := hadm.head; omega))
      have hh1 : 1 ≤ nbit σ - nsh σ := by
        have := hstr.head hnb
        omega
      have hgap := trun_gt_of_pow hwu hdu hbal hh1 (e := k + 1) (by omega)
        (by rw [hru]; exact hfval)
      rw [hru] at hgap
      omega
  · -- the residual digit is a zero bit
    simp only [rstep_V] at hcv
    rw [hbv]
    simp only [qout, rstep_Y]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [pow_zero] at hk
      omega
    · exfalso
      have : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega

/-! ## Lemma C -/

/-- **The refined reading of the drain digits.**  Two changes to `ready_chi`:
the counter in front of the digits is only asked for `4m - 4` — the early
reset cannot promise more — and the debt the scan carries out of the digits is
reported together with the information that either `m` is a power of two (the
digits are all zero) or the debt is smaller by eight. -/
theorem ready_chi_ref : ∀ (m : ℕ), 1 ≤ m → ∀ pre : List RB, CStack (TW pre) →
    4 * m ≤ cval (TW pre) + 4 →
    (∀ n : ℕ, n + 4 ≤ 4 * m → (n % 2 = 1 → n + 9 ≤ 2 * m) →
      ((∃ k, m = 2 ^ k) ∨ n + 12 ≤ 4 * m) → Ready (dpow n (TW pre))) →
    Ready (TW (pre ++ chi m)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm pre hst hval hcont
      rcases lt_or_ge m 2 with hlt | hge
      · obtain rfl : m = 1 := by omega
        rw [chi_of_lt (by omega)]
        simpa using hcont 0 (by omega) (by omega) (Or.inl ⟨0, rfl⟩)
      · have hm'1 : 1 ≤ m / 2 := by omega
        have hm'lt : m / 2 < m := by omega
        rw [chi_of_le hge]
        by_cases hpar : m % 2 = 0
        · -- an even digit: a pop matched to a zero bit
          rw [if_pos hpar]
          have h2 : 2 ≤ cval (TW pre) := by omega
          have hvalX : cval (TW (pre ++ [RB.X])) = (cval (TW pre) - 2) / 2 := cval_TW_X hst h2
          have hrun : Ready (TW ((pre ++ [RB.X]) ++ chi (m / 2))) := by
            refine ih (m / 2) hm'lt hm'1 (pre ++ [RB.X]) (CStack_TW_X hst) (by omega) ?_
            intro n hn _ hdisj
            refine ready_X hst (by omega) ?_
            refine hcont (2 * n + 4) (by omega) (by omega) ?_
            rcases hdisj with ⟨k, hk⟩ | hd
            · exact Or.inl ⟨k + 1, by rw [pow_succ]; omega⟩
            · exact Or.inr (by omega)
          simpa using hrun
        · -- an odd digit: a pop matched to a one bit
          rw [if_neg hpar]
          have hvalV : cval (TW (pre ++ [RB.V])) = 2 * cval (TW pre) := cval_TW_V pre
          have hrun : Ready (TW ((pre ++ [RB.V]) ++ chi (m / 2))) := by
            refine ih (m / 2) hm'lt hm'1 (pre ++ [RB.V]) (CStack_TW_V hst) (by omega) ?_
            intro n hn _ _
            by_cases hp : n % 2 = 1
            · exact ready_V_odd hp
            · refine ready_V_even (by omega) ?_
              refine hcont (n / 2) (by omega) (by omega) (Or.inr (by omega))
          simpa using hrun

/-- **Lemma C**: the word the early clean reset rebuilds is positive and
ready. -/
theorem lemmaC {t : List LB} (hg : Good t)
    (hslack : ∀ k : ℕ, cval t + 1 = 2 ^ k → (cval t : ℤ) + 1 ≤ bval t)
    {w : List RB} {h : ℕ} (hgen : Gen w h) :
    1 ≤ rrun (wordCD t w h) 0 ∧ Ready (TW (wordCD t w h)) := by
  have hxB : (cval t : ℤ) ≤ bval t := hg.head
  have hB0 : (0 : ℤ) ≤ bval t := le_trans (Int.natCast_nonneg _) hxB
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  -- the digits of the drain, and the buffer they begin with
  have hchi : chi (2 ^ (h + 1) * (cval t + 1))
      = List.replicate (h + 1) RB.X ++ chi (cval t + 1) :=
    chi_two_pow (h + 1) (cval t + 1) (by omega)
  have hword : wordCD t w h
      = ((pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) ++ chi (cval t + 1))
        ++ [RB.V] := by
    rw [wordCD, hchi]
    simp [List.append_assoc]
  have hdigs : Digs (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) :=
    (((pdec_digs t).append (digs_singleton (Or.inl rfl))).append hgen.digs).append
      (digs_Xrun (h + 1))
  -- the value in front of the digits
  have hval0 : rrun (pdec t ++ [RB.Y]) 0 = 2 * bval t + 1 := by
    rw [rrun_append, ← bval_eq_rrun]
    simp
  have hpre : rrun (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) 0
      = rrun (w ++ List.replicate (h + 1) RB.X) (2 * bval t + 1) := by
    rw [show pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X
      = (pdec t ++ [RB.Y]) ++ (w ++ List.replicate (h + 1) RB.X) by simp, rrun_append, hval0]
  have hF : 4 * bval t ≤ rrun (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) 0 := by
    rw [hpre]
    have := gen_rrun_buf' hgen (2 * bval t + 1) (by omega)
    omega
  constructor
  · -- positivity
    rw [hword, rrun_append, rrun_append]
    rcases Nat.eq_zero_or_pos (cval t) with hx0 | hx1
    · -- the digits are empty, and the dyadic slack gives a positive value
      have hB1 : (1 : ℤ) ≤ bval t := by
        have := hslack 0 (by simp [hx0])
        rw [hx0] at this
        simpa using this
      rw [hx0, chi_of_lt (by omega)]
      simp only [rrun_nil, rrun_cons, rstep_V]
      omega
    · have hpos : 1 ≤ rrun (chi (cval t + 1))
          (rrun (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) 0) := by
        refine rrun_chi_pos_entry (by omega) ?_
        push_cast
        omega
      simp only [rrun_cons, rrun_nil, rstep_V]
      omega
  · -- readiness
    -- the paid stack of the decoded word of `t`
    have hclt : (0 : ℤ) ≤ rrun (pdec t) (cval ([LB.L] : List LB)) := by
      rw [hL, Nat.cast_zero, ← bval_eq_rrun]
      exact hB0
    obtain ⟨hstt, hadmt, hgt, -, -, -⟩ :=
      tfold_props (pdec t) (pdec_digs t) (σ := [LB.L]) CStack.base adm_L good_L hclt
    have hcvp : (cval (TW (pdec t)) : ℤ) = bval t := cval_TW_pdec hg
    -- the paid stack in front of the digits
    have hclpre : (0 : ℤ) ≤ rrun (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X)
        (cval ([LB.L] : List LB)) := by
      rw [hL, Nat.cast_zero]
      omega
    obtain ⟨hstpre, -, -, hcvpre, -, -⟩ :=
      tfold_props _ hdigs (σ := [LB.L]) CStack.base adm_L good_L hclpre
    have hcvpre' : (cval (TW (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X)) : ℤ)
        = rrun (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X) 0 := by
      rw [TW, hcvpre, hL, Nat.cast_zero]
    rw [hword]
    refine ready_V_even (u := (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X)
      ++ chi (cval t + 1)) (n := 0) rfl ?_
    simp only [Nat.zero_div, dpow_zero]
    refine ready_chi_ref (cval t + 1) (by omega) _ hstpre (by omega) ?_
    intro n hn _ hdisj
    -- the debt the digits leave is paid for by the decoded value of `t`
    have hn4B : (n : ℤ) + 4 ≤ 4 * bval t := by
      rcases hdisj with ⟨k, hk⟩ | hd
      · have := hslack k (by omega)
        omega
      · omega
    -- the scan of the middle part over the paid stack of `P(t)`
    have hsplit : pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X
        = pdec t ++ (([RB.Y] ++ (w ++ List.replicate h RB.X)) ++ [RB.X]) := by
      rw [List.replicate_succ']
      simp
    have hfold : TW (pdec t ++ [RB.Y] ++ w ++ List.replicate (h + 1) RB.X)
        = tfold (TW (pdec t)) (([RB.Y] ++ (w ++ List.replicate h RB.X)) ++ [RB.X]) := by
      rw [hsplit, TW, tfold_append, TW]
    rw [hfold]
    have hdigs2 : Digs (([RB.Y] ++ (w ++ List.replicate h RB.X)) ++ [RB.X]) :=
      ((digs_singleton (Or.inl rfl)).append (hgen.digs.append (digs_Xrun h))).append
        (digs_singleton (Or.inr (Or.inr rfl)))
    have hbuf := gen_rrun_buf hgen (2 * bval t + 1) (by omega)
    have hvalY : rrun [RB.Y] (cval (TW (pdec t)) : ℤ) = 2 * bval t + 1 := by
      rw [show rrun [RB.Y] (cval (TW (pdec t)) : ℤ) = 2 * (cval (TW (pdec t)) : ℤ) + 1 from rfl,
        hcvp]
    refine ready_scan _ hdigs2 hstt hadmt hgt ?_ ?_
      (fun n' hn' => ready_dpow_of_cval hg hn')
    · -- the whole middle part is clean
      rw [rrun_append, rrun_append, hvalY]
      simp only [rrun_cons, rrun_nil, rstep_X]
      omega
    · -- the scan
      refine Scan_snoc_X.mpr ⟨?_, ?_⟩
      · rw [rrun_append, hvalY]
        push_cast
        omega
      refine Scan_append_of _ (hgen.digs.append (digs_Xrun h)) _ ?_
      rw [hvalY]
      refine gen_scan_gap hgen (2 * bval t + 1) (2 * n + 4) _ (by push_cast; omega) ?_
      intro m hm
      exact Scan_single_Y (fun _ => by omega)

end BB25.Prefix
