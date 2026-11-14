/-
# The exact checkpoint a drain reaches

The return theorem of `Drain.lean` only records *that* the machine comes back
to a safe checkpoint.  For `1LA` the identity of the checkpoint is needed, so
this file redoes the drain keeping track of the reset word:

* `exact_zero`: an exhausted counter deposits its decoded word, the reset
  rebuilds the paid stack of `P(σ) V`, and that is the checkpoint;
* `exact_drain`: a whole drain emits the digits `chi (cval σ + 1)` on the way,
  so the checkpoint is the paid stack of `P(σ) chi(cval σ + 1) V`;
* `exact_tail`: a pending `2>` in front of a run of `22` blocks first pushes
  the run and pops one bit, which adds `Y^r V` to the word and multiplies the
  drain counter by `2^(r-1)`.

The last two are the exact form of Section 5 of the submitted argument: the
`X^(r-1)` buffer of the document is the head of `chi (2^(r-1) m)`.
-/
import RequestProject.BB25.Prefix.LA.Direct

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The overflow at an exhausted counter -/

/-- **The exact checkpoint of an exhausted counter.** -/
theorem exact_zero {σ : List LB} (hst : CStack σ) (hv : cval σ = 0) (hb2 : (1 : ℤ) ≤ bval σ) :
    SafeCP (TW (pdec σ ++ [.V])) ∧ Strict (TW (pdec σ ++ [.V])) ∧
      ∃ k, BRun b4 ⟨σ, .Rt, [.R]⟩ (cpCfg (TW (pdec σ ++ [.V]))) k := by
  have hs1 : bstep b4 ⟨σ, .Rt, [.R]⟩ = some (⟨σ, .Lt, [.V, .R]⟩, 3) := rfl
  obtain ⟨k1, hr1⟩ := brun_overflow_of (b4 := b4) hst hv [.V, .R]
  rw [ofw_eq_pdec hst hv] at hr1
  have hs2 : bstep b4 ⟨[.L], .Lt, pdec σ ++ [.V, .R]⟩
      = some (⟨[.L], .Rt, .P2 :: (pdec σ ++ [.V, .R])⟩, 4) := rfl
  set w : List RB := pdec σ ++ [RB.V] with hw
  have hwd : Digs w := by
    refine (pdec_digs σ).append ?_
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact Or.inr (Or.inl rfl)
  have hrw : rrun w 0 = 2 * bval σ := by
    rw [hw, rrun_append, ← bval_eq_rrun]
    simp
  have hcl : 0 ≤ rrun w (cval (paid true [LB.L])) := by
    simp only [paid_true]
    have : cval ([LB.L] : List LB) = 0 := rfl
    rw [this]
    simp only [Nat.cast_zero, hrw]
    omega
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hwd true [.L] CStack.base (by simp) hcl [.R]
  obtain ⟨hst', hadm', hg', hcv', -, -⟩ :=
    tfold_props w hwd (σ := [LB.L]) CStack.base adm_L good_L (by simpa using hcl)
  have hpaid' : paid p' phys = TW w := by simpa [TW] using hpaid
  have hcvπ : (cval (TW w) : ℤ) = 2 * bval σ := by
    have : (cval (TW w) : ℤ) = rrun w (cval ([LB.L] : List LB)) := hcv'
    rw [this, show cval ([LB.L] : List LB) = 0 from rfl]
    simpa using hrw
  obtain ⟨k2, hr2⟩ := brun_end (b4 := b4) p' phys hstp (by
    intro hpf
    have := hcvp hpf
    omega)
  rw [hpaid'] at hr2
  have hendX : ∃ t, TW w = LB.X :: t :=
    ⟨TW (pdec σ), by rw [TW, hw, tfold_append]; rfl⟩
  refine ⟨⟨hst', hadm', hg', by omega, hendX⟩, strict_TW hwd (by simpa using hcl),
    ⟨3 + (k1 + (4 + (k + k2))), ?_⟩⟩
  have happ : w ++ [RB.R] = pdec σ ++ [RB.V, RB.R] := by
    rw [hw, List.append_assoc]
    rfl
  have hrun' : BRun b4 ⟨[LB.L], .Rt, .P2 :: (pdec σ ++ [.V, .R])⟩
      ⟨phys, .Rt, pd p' :: [RB.R]⟩ k := by
    rw [← happ]
    exact hrun
  exact BRun.head hs1 (hr1.trans (BRun.head hs2 (hrun'.trans hr2)))

/-! ## The drain -/

/-- **The exact checkpoint of a drain.**  Each round halves `cval + 1` and
emits one digit, so the word of the whole drain is `chi (cval σ + 1)`. -/
theorem exact_drain : ∀ (n : ℕ) (σ : List LB), cval σ ≤ n → Strong σ →
    SafeCP (TW (pdec σ ++ chi (cval σ + 1) ++ [.V])) ∧
      Strict (TW (pdec σ ++ chi (cval σ + 1) ++ [.V])) ∧
      ∃ k, BRun b4 ⟨σ, .Rt, [.R]⟩ (cpCfg (TW (pdec σ ++ chi (cval σ + 1) ++ [.V]))) k := by
  intro n
  induction n with
  | zero =>
      intro σ hn h
      have hv : cval σ = 0 := by omega
      have hb : (1 : ℤ) ≤ bval σ := by
        have := h.bound
        rw [hv] at this
        simpa using by omega
      rw [hv, chi_of_lt (by omega)]
      simpa using exact_zero (b4 := b4) h.st hv hb
  | succ n ih =>
      intro σ hn h
      rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
      · have hb : (1 : ℤ) ≤ bval σ := by
          have := h.bound
          rw [h0] at this
          simpa using by omega
        rw [h0, chi_of_lt (by omega)]
        simpa using exact_zero (b4 := b4) h.st h0 hb
      · -- one round of the drain
        have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval h.st h1
        have hbv : bval (cdec σ) = bval σ := bval_cdec h.st h1
        have hstd : CStack (cdec σ) := cdec_CStack_all h.st
        have hadmd : Adm (cdec σ) := Adm.cdec h.st h.adm h1
        have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched h.st h.adm h1
        have hB : 3 * ((cval σ : ℤ) + 1) ≤ bval σ + 2 := h.bound
        have hs1 : bstep b4 ⟨σ, .Rt, [.R]⟩ = some (⟨σ, .Lt, [.V, .R]⟩, 3) := rfl
        obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) h.st h1 [.V, .R]
        have hs2 : bstep b4 ⟨cdec σ, .Rt, [.V, .R]⟩
            = some (⟨.W :: cdec σ, .Rt, [.R]⟩, 2) := rfl
        have hrun0 : BRun b4 ⟨σ, .Rt, [.R]⟩ ⟨.W :: cdec σ, .Rt, [.R]⟩ (3 + (k1 + 2)) :=
          BRun.head hs1 (hr1.trans (BRun.of_step hs2))
        have hstrong : Strong (.W :: cdec σ) := by
          refine ⟨hstd.consW, adm_consW hadmd ?_, ?_⟩
          · rw [nbit_cdec, nsh_cdec]
            omega
          · simp only [cval_W, bval_W, hcv, hbv]
            by_cases hodd : (cval σ - 1) % 2 = 1
            · simp only [hodd, if_pos]
              omega
            · simp only [hodd, if_false]
              omega
        have hnext : cval (.W :: cdec σ) ≤ n := by
          simp only [cval_W, hcv]
          omega
        -- the word of the round
        have hword : pdec (.W :: cdec σ) ++ chi (cval (.W :: cdec σ) + 1)
            = pdec σ ++ chi (cval σ + 1) := by
          have hpd : pdec (cdec σ) = pdec σ := pdec_cdec h.st h1
          have hcv2 : cval (.W :: cdec σ) + 1 = (cval σ + 1) / 2 := by
            simp only [cval_W, hcv]
            omega
          have hdig : (if cval (cdec σ) % 2 = 1 then RB.V else RB.X)
              = (if (cval σ + 1) % 2 = 0 then RB.X else RB.V) := by
            by_cases he : cval σ % 2 = 0
            · have h1' : cval (cdec σ) % 2 = 1 := by
                rw [hcv]
                omega
              rw [if_pos h1', if_neg (by omega)]
            · have h1' : cval (cdec σ) % 2 = 0 := by
                rw [hcv]
                omega
              rw [if_neg (by omega), if_pos (by omega)]
          have hchi : chi (cval σ + 1)
              = (if (cval σ + 1) % 2 = 0 then RB.X else RB.V) :: chi ((cval σ + 1) / 2) :=
            chi_of_le (by omega)
          rw [pdec_W, hpd, hdig, hcv2, hchi, List.append_assoc]
          rfl
        obtain ⟨hcp, hstr, k, hrun⟩ := ih (.W :: cdec σ) hnext hstrong
        rw [hword] at hcp hstr hrun
        exact ⟨hcp, hstr, ⟨(3 + (k1 + 2)) + k, hrun0.trans hrun⟩⟩

/-! ## The pending-`2>` tail -/

/-- **The exact checkpoint of a pending-`2>` tail.**  The pending digit pushes
the run of `22` blocks as one bits, the terminal `1` turns the head around and
one bit is popped; the drain then runs on a counter multiplied by `2^(r-1)`. -/
theorem exact_tail {σ : List LB} (hst : CStack σ) (hadm : Adm σ)
    (hb : 3 * ((cval σ : ℤ) + 1) ≤ 4 * (bval σ + 1)) {r : ℕ} (hr : 1 ≤ r) :
    SafeCP (TW (pdec σ ++ List.replicate r .Y ++ [.V]
        ++ chi (2 ^ (r - 1) * (cval σ + 1)) ++ [.V])) ∧
      Strict (TW (pdec σ ++ List.replicate r .Y ++ [.V]
        ++ chi (2 ^ (r - 1) * (cval σ + 1)) ++ [.V])) ∧
      ∃ k, BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩
        (cpCfg (TW (pdec σ ++ List.replicate r .Y ++ [.V]
          ++ chi (2 ^ (r - 1) * (cval σ + 1)) ++ [.V]))) k := by
  set π : List LB := List.replicate r LB.Z ++ σ with hπ
  have hstπ : CStack π := CStack_Zrun _ hst
  have hadmπ : Adm π := Adm_Zrun _ hadm
  obtain ⟨hcount1, hcount2⟩ := nbit_Zrun r σ
  set N : ℕ := 2 ^ r * (cval σ + 1) with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcπ : cval π = N - 1 := by rw [hπ, cval_Zrun, hN]
  set M : ℤ := 2 ^ r * (bval σ + 1) with hM
  have hbπ : bval π = M - 1 := by rw [hπ, bval_Zrun, hM]
  have hNeven : 2 ∣ N := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hodd : cval π % 2 = 1 := by omega
  have hNM : 3 * (N : ℤ) ≤ 4 * M := by
    have h2 : (0:ℤ) < 2 ^ r := by positivity
    have hNcast : (N : ℤ) = 2 ^ r * ((cval σ : ℤ) + 1) := by rw [hN]; push_cast; ring
    rw [hNcast, hM]
    calc 3 * (2 ^ r * ((cval σ : ℤ) + 1)) = 2 ^ r * (3 * ((cval σ : ℤ) + 1)) := by ring
      _ ≤ 2 ^ r * (4 * (bval σ + 1)) := by
          exact mul_le_mul_of_nonneg_left hb (le_of_lt h2)
      _ = 4 * (2 ^ r * (bval σ + 1)) := by ring
  have hrun1 : BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩
      ⟨π, .Rt, .P2 :: [.R1]⟩ (2 * r) := brun_P2_Yrun _ _ _
  have hs1 : bstep b4 ⟨π, .Rt, [.P2, .R1]⟩ = some (⟨π, .Rt, [.V, .R]⟩, 0) := rfl
  have hs2 : bstep b4 ⟨π, .Rt, [.V, .R]⟩ = some (⟨.W :: π, .Rt, [.R]⟩, 2) := rfl
  have hrun : BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩
      ⟨.W :: π, .Rt, [.R]⟩ (2 * r + (0 + 2)) :=
    hrun1.trans (BRun.head hs1 (BRun.of_step hs2))
  -- the resulting configuration is strong
  have hcW : cval (.W :: π) = N / 2 - 1 := by
    simp only [cval_W, hcπ]
    omega
  have hbW : bval (.W :: π) = 2 * (M - 1) := by
    rw [bval_W, if_pos hodd, hbπ]
  have hstrong : Strong (.W :: π) := by
    refine ⟨hstπ.consW, adm_consW hadmπ ?_, ?_⟩
    · have h3 := hadm.head
      rw [hcount1, hcount2]
      omega
    · rw [hcW, hbW]
      have hcast : ((N / 2 - 1 : ℕ) : ℤ) = (N : ℤ) / 2 - 1 := by omega
      rw [hcast]
      omega
  -- the word of the tail
  have hpdW : pdec (.W :: π) = pdec σ ++ List.replicate r .Y ++ [.V] := by
    rw [pdec_W, if_pos hodd, hπ, pdec_Zrun]
  have hcvW : cval (.W :: π) + 1 = 2 ^ (r - 1) * (cval σ + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hNv : N = 2 * (2 ^ m * (cval σ + 1)) := by
      rw [hN]
      ring
    have hpos : 1 ≤ 2 ^ m * (cval σ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simp only [hcW, Nat.add_sub_cancel]
    omega
  obtain ⟨hcp, hstr, k, hrunD⟩ :=
    exact_drain (b4 := b4) (cval (.W :: π)) (.W :: π) (le_refl _) hstrong
  rw [hpdW, hcvW] at hcp hstr hrunD
  exact ⟨hcp, hstr, ⟨(2 * r + (0 + 2)) + k, hrun.trans hrunD⟩⟩

end BB25.Prefix
