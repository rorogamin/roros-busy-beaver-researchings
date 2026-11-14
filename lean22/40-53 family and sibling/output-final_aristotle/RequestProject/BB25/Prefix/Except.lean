/-
# The pieces shared by the members `0LA` and `2LB`

Both of these members answer the `241` block by turning the head around with a
pending `1>` behind a residual digit, and for both of them the sweep that finds
a pop over a counter of value exactly two runs into an *exceptional* checkpoint
whose stack need no longer be good.

This file collects the machine runs that the two arguments have in common:

* `brun_to_G` — the two decrements that bring the head from the `141` block to
  the `241` block;
* `brun_overflow_reset` — an exhausted counter deposits its decoded word and
  the head starts the reset;
* `brun_pd_P1`, `brun_pd_U` — how a pending digit crosses the residual `1>` and
  `12` blocks, paying the pending decrement;
* `brun_Yrun_cp` — the run of `22` blocks in front of the terminal `1` leads to
  the next `<B1` checkpoint, whose stack is `11` over `01^(r-1)`;
* the three single steps of a `<B1` sweep.
-/
import RequestProject.BB25.Prefix.Return
import RequestProject.BB25.Prefix.Expand

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Reaching the `241` block -/

/-- Two decrements bring the head from the `141` block to the `241` block. -/
theorem brun_to_G {c : List LB} (hst : CStack c) (hv : 2 ≤ cval c) (rest : List RB) :
    ∃ k, BRun b4 ⟨c, .Lt, .F :: rest⟩ ⟨cdec (cdec c), .Rt, .G :: rest⟩ k := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.F :: rest)
  have hsF : bstep b4 ⟨cdec c, .Rt, .F :: rest⟩ = some (⟨cdec c, .Lt, .G :: rest⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.G :: rest)
  exact ⟨k1 + (1 + k2), hr1.trans (BRun.head hsF hr2)⟩

/-! ## Crossing the residual digits -/

/-- A pending digit in front of a pending `1>`: the two merge into a `21`
block, which the head crosses by pushing a pop; a pending `1>` pays its debt
first. -/
theorem brun_pd_P1 {p : Bool} {phys : List LB} (hst : CStack phys)
    (hcv : p = false → 1 ≤ cval phys) (rest : List RB) :
    ∃ k, BRun b4 ⟨phys, .Rt, pd p :: .P1 :: rest⟩ ⟨.W :: paid p phys, .Rt, rest⟩ k := by
  cases p with
  | true =>
      refine ⟨0 + 2, BRun.head (c₁ := ⟨phys, .Rt, RB.V :: rest⟩) ?_ (BRun.of_step ?_)⟩
      · exact (show bstep b4 ⟨phys, .Rt, .P2 :: .P1 :: rest⟩
          = some (⟨phys, .Rt, .V :: rest⟩, 0) from rfl)
      · exact (show bstep b4 ⟨phys, .Rt, RB.V :: rest⟩
          = some (⟨.W :: phys, .Rt, rest⟩, 2) from rfl)
  | false =>
      obtain ⟨k, hrk⟩ := brun_cdec_of (b4 := b4) hst (hcv rfl) (.V :: rest)
      refine ⟨0 + (1 + (k + 2)), BRun.head (c₁ := ⟨phys, .Rt, RB.X :: rest⟩) ?_
        (BRun.head (c₁ := ⟨phys, .Lt, RB.V :: rest⟩) ?_ (hrk.trans (BRun.of_step ?_)))⟩
      · exact (show bstep b4 ⟨phys, .Rt, .P1 :: .P1 :: rest⟩
          = some (⟨phys, .Rt, .X :: rest⟩, 0) from rfl)
      · exact (show bstep b4 ⟨phys, .Rt, RB.X :: rest⟩
          = some (⟨phys, .Lt, .V :: rest⟩, 1) from rfl)
      · exact (show bstep b4 ⟨cdec phys, .Rt, RB.V :: rest⟩
          = some (⟨.W :: cdec phys, .Rt, rest⟩, 2) from rfl)

/-- A pending digit in front of a `12` block: the head crosses it by pushing a
pop, and the pending digit becomes a paid `2>`. -/
theorem brun_pd_U {p : Bool} {phys : List LB} (hst : CStack phys)
    (hcv : p = false → 1 ≤ cval phys) (rest : List RB) :
    ∃ k, BRun b4 ⟨phys, .Rt, pd p :: .U :: rest⟩ ⟨.W :: paid p phys, .Rt, .P2 :: rest⟩ k := by
  cases p with
  | true =>
      refine ⟨0 + 2, BRun.head (c₁ := ⟨phys, .Rt, RB.V :: .P2 :: rest⟩) ?_ (BRun.of_step ?_)⟩
      · exact (show bstep b4 ⟨phys, .Rt, .P2 :: .U :: rest⟩
          = some (⟨phys, .Rt, .V :: .P2 :: rest⟩, 0) from rfl)
      · exact (show bstep b4 ⟨phys, .Rt, RB.V :: .P2 :: rest⟩
          = some (⟨.W :: phys, .Rt, .P2 :: rest⟩, 2) from rfl)
  | false =>
      obtain ⟨k, hrk⟩ := brun_cdec_of (b4 := b4) hst (hcv rfl) (.V :: .P2 :: rest)
      refine ⟨0 + (1 + (k + 2)), BRun.head (c₁ := ⟨phys, .Rt, RB.X :: .P2 :: rest⟩) ?_
        (BRun.head (c₁ := ⟨phys, .Lt, RB.V :: .P2 :: rest⟩) ?_ (hrk.trans (BRun.of_step ?_)))⟩
      · exact (show bstep b4 ⟨phys, .Rt, .P1 :: .U :: rest⟩
          = some (⟨phys, .Rt, .X :: .P2 :: rest⟩, 0) from rfl)
      · exact (show bstep b4 ⟨phys, .Rt, RB.X :: .P2 :: rest⟩
          = some (⟨phys, .Lt, .V :: .P2 :: rest⟩, 1) from rfl)
      · exact (show bstep b4 ⟨cdec phys, .Rt, RB.V :: .P2 :: rest⟩
          = some (⟨.W :: cdec phys, .Rt, .P2 :: rest⟩, 2) from rfl)

/-! ## Reaching the next checkpoint -/

/-- The head swallows the run of `22` blocks, turns at the terminal `1` and
reaches the next `<B1` checkpoint; the decrement on the way back turns the
lowest one bit into a zero bit. -/
theorem brun_Yrun_cp {π : List LB} (hst : CStack π) {r : ℕ} (hr : 1 ≤ r) :
    ∃ k, BRun b4 ⟨π, .Rt, List.replicate r .Y ++ [.R1]⟩
      ⟨.X :: (List.replicate (r - 1) .Z ++ π), .Bt, [.Y, .R1]⟩ k := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  set ρ : List LB := List.replicate (m + 1) LB.Z ++ π with hρ
  have hstρ : CStack ρ := CStack_Zrun _ hst
  have hcρ : cval ρ = 2 ^ (m + 1) * (cval π + 1) - 1 := cval_Zrun _ _
  have hmul : 2 ≤ 2 ^ (m + 1) * (cval π + 1) := by
    have hpow : 2 ≤ 2 ^ (m + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans hpow (Nat.le_mul_of_pos_right _ (by omega))
  have h1 : 1 ≤ cval ρ := by omega
  have hcdec : cdec ρ = .X :: (List.replicate m .Z ++ π) := by
    rw [hρ, List.replicate_succ, List.cons_append, cdec_Z]
  obtain ⟨k, hrk⟩ := brun_cdec_of (b4 := b4) hstρ h1 [.R2]
  rw [hcdec] at hrk
  refine ⟨2 * (m + 1) + (1 + (k + 11)), ?_⟩
  have hrun1 : BRun b4 ⟨π, .Rt, List.replicate (m + 1) .Y ++ [.R1]⟩ ⟨ρ, .Rt, [.R1]⟩ (2 * (m + 1)) :=
    brun_Yrun _ _ _
  refine hrun1.trans (BRun.head ?_ (hrk.trans (BRun.of_step ?_)))
  · exact (show bstep b4 ⟨ρ, .Rt, [RB.R1]⟩ = some (⟨ρ, .Lt, [.R2]⟩, 1) from rfl)
  · exact (show bstep b4 ⟨.X :: (List.replicate m LB.Z ++ π), .Rt, [RB.R2]⟩
      = some (⟨.X :: (List.replicate m LB.Z ++ π), .Bt, [.Y, .R1]⟩, 11) from rfl)

/-! ## The single steps of a `<B1` sweep -/

theorem brun_Bt_X (s : List LB) :
    BRun b4 ⟨.X :: s, .Bt, [.Y, .R1]⟩ ⟨s, .Bt, List.replicate 2 .Y ++ [.R1]⟩ 6 :=
  BRun.of_step rfl

theorem brun_Bt_Z (s : List LB) (tail : List RB) :
    BRun b4 ⟨.Z :: s, .Bt, tail⟩ ⟨s, .Lt, .X :: .P2 :: tail⟩ 4 :=
  BRun.of_step rfl

theorem brun_Bt_W (s : List LB) (tail : List RB) :
    BRun b4 ⟨.W :: s, .Bt, tail⟩ ⟨s, .Lt, .F :: tail⟩ 2 :=
  BRun.of_step rfl

/-! ## The word deposited by an exhausted counter of value two -/

/-- What the reset of the word `pdec c` builds, when `c` is a good admissible
counter stack of value two: a good stack `t` whose counter is the decoded value
of `c`, whose own decoded value is at least its counter, and which is subject
to the dichotomy of `Expand.lean`. -/
theorem paid_stack_facts {c : List LB} (hadm : Adm c) (hg : Good c)
    (hh : 2 ≤ nbit c - nsh c) :
    CStack (tfold [LB.L] (pdec c)) ∧ Adm (tfold [LB.L] (pdec c)) ∧
      Good (tfold [LB.L] (pdec c)) ∧
      (cval (tfold [LB.L] (pdec c)) : ℤ) = bval c ∧
      bval (tfold [LB.L] (pdec c)) = trun (pdec c) 0 0 ∧
      ((cval (tfold [LB.L] (pdec c)) : ℤ) % 2 = 1 ∨
        11 ≤ bval (tfold [LB.L] (pdec c))) := by
  have hb0 : (0 : ℤ) ≤ bval c := le_trans (Int.natCast_nonneg _) hg.head
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hcl : 0 ≤ rrun (pdec c) (cval ([LB.L] : List LB)) := by
    rw [hL]
    simpa [hru] using hb0
  obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, -⟩ :=
    tfold_props (pdec c) (pdec_digs c) (σ := [LB.L]) CStack.base adm_L good_L hcl
  have hcv : (cval (tfold [LB.L] (pdec c)) : ℤ) = bval c := by
    rw [hcvt, hL, Nat.cast_zero, hru]
  have hbv : bval (tfold [LB.L] (pdec c)) = trun (pdec c) 0 0 := by
    rw [hbvt, hL, Nat.cast_zero]
    rfl
  refine ⟨hstt, hadmt, hgt, hcv, hbv, ?_⟩
  -- the dichotomy: either the decoded word has no close at all, and then its
  -- value is `2 ^ n - 1`, or it has one, and the height bound applies
  by_cases hcl2 : HasCl (pdec c)
  · refine Or.inr ?_
    have hq : 1 ≤ qcnt (pdec c) 0 :=
      qcnt_pos_of_hasCl (pdec_digs c) (pdec_dyck hadm) hcl2 0
    have hbal : bal (pdec c) = ((nbit c - nsh c : ℕ) : ℤ) := by
      rw [bal_pdec]
      have := hadm.head
      omega
    have hbound := trun_ge_pow_q1 (pdec_digs c) (pdec_dyck hadm) hbal (le_refl 0) hq
    have hpow : (4 : ℤ) ≤ 2 ^ (nbit c - nsh c) := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (nbit c - nsh c) := by
            exact pow_le_pow_right₀ (by norm_num) hh
    rw [hbv]
    norm_num at hbound
    omega
  · refine Or.inl ?_
    have hrep : pdec c = List.replicate (pdec c).length RB.Y :=
      eq_replicate_Y (pdec_digs c) hcl2
    have hval : rrun (pdec c) 0 = 2 ^ (pdec c).length - 1 := by
      conv_lhs => rw [hrep]
      rw [rrun_replicate_Y]
      ring
    have hdvd : (2 : ℤ) ∣ 2 ^ (pdec c).length * 1 := by
      have hlen : 1 ≤ (pdec c).length := by
        by_contra hc
        obtain hz : pdec c = [] := List.length_eq_zero_iff.mp (by omega)
        have hb0 := bal_pdec c
        rw [hz] at hb0
        have := hadm.head
        simp only [bal_nil] at hb0
        omega
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [hcv, ← hru, hval]
    simp only [mul_one] at hdvd
    omega

/-- **A decoded word whose value is divisible by four has at least two
expanding closes**, hence a large transduced value. -/
theorem paid_stack_mod_four {c : List LB} (hadm : Adm c) (hg : Good c)
    (hh : 2 ≤ nbit c - nsh c) (hm : bval c % 4 = 0) : 43 ≤ bval (tfold [LB.L] (pdec c)) := by
  obtain ⟨-, -, -, -, hbvt, -⟩ := paid_stack_facts hadm hg hh
  have hb0 : (0 : ℤ) ≤ bval c := le_trans (Int.natCast_nonneg _) hg.head
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hbal : bal (pdec c) = ((nbit c - nsh c : ℕ) : ℤ) := by
    rw [bal_pdec]
    have := hadm.head
    omega
  have hq : 2 ≤ qcnt (pdec c) 0 := by
    by_contra hc
    have hne := rrun_mod_four_ne (pdec_digs c) (pdec_dyck hadm) (by rw [hru]; exact hb0)
      (by omega) hbal hh
    rw [hru] at hne
    exact hne hm
  have hbound := trun_ge_pow_q2 (pdec_digs c) (pdec_dyck hadm) hbal (le_refl (0 : ℤ)) hq
  have hpow : (4 : ℤ) ≤ 2 ^ (nbit c - nsh c) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (nbit c - nsh c) := pow_le_pow_right₀ (by norm_num) hh
  rw [hbvt]
  norm_num at hbound
  omega

/-! ## The tail, without goodness -/

/-- **A `22` block in front of a pending `2>`, with no goodness assumption.**
All that is needed is that the decoded value is nonnegative and satisfies the
drain bound. -/
theorem returns_YP2_weak {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hb0 : 0 ≤ bval σ)
    (hb : 3 * (cval σ : ℤ) ≤ 4 * bval σ + 4) (r : ℕ) :
    Returns b4 ⟨σ, .Lt, .Y :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
  · exact returns_overflow hst hadm hb0 h0 (Or.inr (Or.inr rfl)) (Or.inr rfl)
  · have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
    have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
    have hstd : CStack (cdec σ) := cdec_CStack_all hst
    have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.Y :: .P2 :: tail)
    have hs1 : bstep b4 ⟨cdec σ, .Rt, .Y :: .P2 :: tail⟩
        = some (⟨.Z :: cdec σ, .Rt, .P2 :: tail⟩, 2) := rfl
    refine Returns.of_run (hr1.trans (BRun.of_step hs1)) ?_
    refine returns_tail hstd.consZ (adm_consZ hadmd) ?_ (Or.inr (by simp))
    simp only [cval_Z, bval_Z, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hcv, hbv]
    omega

/-- **A pending `1>` in front of the tail, with no goodness assumption.** -/
theorem returns_P1_tail_weak {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hb0 : 0 ≤ bval σ)
    (hb : 3 * (cval σ : ℤ) ≤ 4 * bval σ + 4) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4 ⟨σ, .Rt, .P1 :: (List.replicate r .Y ++ [.R1])⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hsplit : List.replicate (m + 1) RB.Y ++ [RB.R1]
      = RB.Y :: (List.replicate m RB.Y ++ [RB.R1]) := by
    rw [List.replicate_succ, List.cons_append]
  rw [hsplit]
  set tail : List RB := List.replicate m RB.Y ++ [RB.R1] with htail
  refine Returns.of_run (BRun.head (show bstep b4 ⟨σ, .Rt, .P1 :: RB.Y :: tail⟩
      = some (⟨σ, .Rt, .U :: .P2 :: tail⟩, 0) from rfl)
    (BRun.of_step (show bstep b4 ⟨σ, .Rt, RB.U :: .P2 :: tail⟩
      = some (⟨σ, .Lt, .Y :: .P2 :: tail⟩, 1) from rfl))) ?_
  rw [htail]
  exact returns_YP2_weak hst hadm hb0 hb m

end BB25.Prefix
