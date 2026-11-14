/-
# The member `2LB`

Its `A> 241` rule is

```
  A> 241  ⟶  <A 12 1>         (three base steps)
```

so the `241` block is replaced by a residual `12` block and a pending `1>`.
Crossing the `12` block turns the head around once more, which costs one extra
decrement: the member needs *four* decrements before the counter below the pop
has paid for the rule.

Three cases arise at the `W` case of the `<B1` sweep.

* `cval c ≥ 4`: all four decrements are available, the `12` block pushes a bit
  and the pending `1>` runs into the tail (`wcase_2LB_ord_weak`, stated with a
  numerical hypothesis rather than goodness, because the repair of the
  exceptional case needs it in that form).
* `cval c = 3`: the fourth decrement overflows.  The stack deposits its decoded
  word, the reset rebuilds the paid stack `t`, and the residual `22` block of
  the turn pushes a *one* bit — so the stack at the next checkpoint is
  `W :: Z :: t`, which is good because the counter below the pop is odd
  (`wcase_2LB_a3`).
* `cval c = 2`: the third decrement already overflows, and the residual `12`
  block is crossed *after* the reset.  The stack at the next checkpoint is
  `W :: W :: t`: two pops in a row, so goodness can fail.  This is the
  exceptional checkpoint, treated in `returns_WWt`.

As for `0LA`, the exceptional checkpoint is repaired by looking one sweep
further.  The bit-block branch of that sweep needs a lower bound on the
counter, and the only genuinely tight case is a counter divisible by eight;
there the decoded word must have two expanding closes (`paid_stack_mod_four`),
which makes the decoded value — and hence the counter — large enough.
-/
import RequestProject.BB25.Prefix.Except

namespace BB25.Prefix

open BB25

/-! ## The ordinary case: a counter of at least four -/

/-- **The `W` case of the sweep for `2LB`, with a counter of at least four.**
Four decrements are available, the residual `12` block pushes a one bit and the
pending `1>` runs into the tail.  Goodness is not assumed: the numerical bound
`3 cval ≤ 4 bval + 14` is all the tail needs. -/
theorem wcase_2LB_ord_weak {c : List LB} (hst : CStack c) (hadm : Adm c)
    (hb0 : 0 ≤ bval c) (hb : 3 * (cval c : ℤ) ≤ 4 * bval c + 14) (hv : 4 ≤ cval c)
    {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_2LB ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  obtain ⟨k0, hr0⟩ := brun_to_G (b4 := b4_2LB) hst (by omega) tail
  have hst1 : CStack (cdec c) := cdec_CStack_all hst
  have hadm1 : Adm (cdec c) := Adm.cdec hst hadm h1
  have hcv1 : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hbv1 : bval (cdec c) = bval c := bval_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hst2 : CStack (cdec (cdec c)) := cdec_CStack_all hst1
  have hadm2 : Adm (cdec (cdec c)) := Adm.cdec hst1 hadm1 h1'
  have hcv2 : cval (cdec (cdec c)) = cval c - 2 := by rw [cdec_cval hst1 h1', hcv1]; omega
  have hbv2 : bval (cdec (cdec c)) = bval c := by rw [bval_cdec hst1 h1', hbv1]
  have h2' : 1 ≤ cval (cdec (cdec c)) := by omega
  have hst3 : CStack (cdec (cdec (cdec c))) := cdec_CStack_all hst2
  have hadm3 : Adm (cdec (cdec (cdec c))) := Adm.cdec hst2 hadm2 h2'
  have hcv3 : cval (cdec (cdec (cdec c))) = cval c - 3 := by rw [cdec_cval hst2 h2', hcv2]; omega
  have hbv3 : bval (cdec (cdec (cdec c))) = bval c := by rw [bval_cdec hst2 h2', hbv2]
  have h3' : 1 ≤ cval (cdec (cdec (cdec c))) := by omega
  have hst4 : CStack (cdec (cdec (cdec (cdec c)))) := cdec_CStack_all hst3
  have hadm4 : Adm (cdec (cdec (cdec (cdec c)))) := Adm.cdec hst3 hadm3 h3'
  have hcv4 : cval (cdec (cdec (cdec (cdec c)))) = cval c - 4 := by
    rw [cdec_cval hst3 h3', hcv3]; omega
  have hbv4 : bval (cdec (cdec (cdec (cdec c)))) = bval c := by rw [bval_cdec hst3 h3', hbv3]
  -- the rule, the turn at the `12` block and the last two decrements
  have hsG : bstep b4_2LB ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .U :: .P1 :: tail⟩, 3) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_2LB) hst2 h2' (.U :: .P1 :: tail)
  have hsU : bstep b4_2LB ⟨cdec (cdec (cdec c)), .Rt, RB.U :: .P1 :: tail⟩
      = some (⟨cdec (cdec (cdec c)), .Lt, .Y :: .P1 :: tail⟩, 1) := rfl
  obtain ⟨k3, hr3⟩ := brun_cdec_of (b4 := b4_2LB) hst3 h3' (.Y :: .P1 :: tail)
  have hsY : bstep b4_2LB ⟨cdec (cdec (cdec (cdec c))), .Rt, RB.Y :: .P1 :: tail⟩
      = some (⟨.Z :: cdec (cdec (cdec (cdec c))), .Rt, .P1 :: tail⟩, 2) := rfl
  refine Returns.of_run
    (hr0.trans (BRun.head hsG (hr2.trans (BRun.head hsU (hr3.trans (BRun.of_step hsY)))))) ?_
  rw [htail]
  refine returns_P1_tail_weak hst4.consZ (adm_consZ hadm4) ?_ ?_ hr
  · simp only [bval_Z, hbv4]
    omega
  · simp only [cval_Z, bval_Z, hbv4, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hcv4]
    omega

/-- The ordinary case under the invariant. -/
theorem wcase_2LB_ord {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : 4 ≤ cval c) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_2LB ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  have hh := hg.head
  have h0 : (0 : ℤ) ≤ (cval c : ℤ) := Int.natCast_nonneg _
  exact wcase_2LB_ord_weak hst hadm (by omega) (by omega) hv hr

/-! ## The counter three: an overflow with a residual `22` block -/

/-- **The `W` case of the sweep for `2LB`, with a counter of exactly three.**
The fourth decrement overflows; after the reset the residual `22` block of the
turn pushes a one bit, so the counter below the final pop is odd and the stack
at the next checkpoint is good. -/
theorem wcase_2LB_a3 {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : cval c = 3) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_2LB ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  obtain ⟨k0, hr0⟩ := brun_to_G (b4 := b4_2LB) hst (by omega) tail
  have hst1 : CStack (cdec c) := cdec_CStack_all hst
  have hadm1 : Adm (cdec c) := Adm.cdec hst hadm h1
  have hcv1 : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hpd1 : pdec (cdec c) = pdec c := pdec_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hst2 : CStack (cdec (cdec c)) := cdec_CStack_all hst1
  have hadm2 : Adm (cdec (cdec c)) := Adm.cdec hst1 hadm1 h1'
  have hcv2 : cval (cdec (cdec c)) = 1 := by rw [cdec_cval hst1 h1', hcv1]; omega
  have hpd2 : pdec (cdec (cdec c)) = pdec c := by rw [pdec_cdec hst1 h1', hpd1]
  have h2' : 1 ≤ cval (cdec (cdec c)) := by omega
  have hst3 : CStack (cdec (cdec (cdec c))) := cdec_CStack_all hst2
  have hadm3 : Adm (cdec (cdec (cdec c))) := Adm.cdec hst2 hadm2 h2'
  have hcv3 : cval (cdec (cdec (cdec c))) = 0 := by rw [cdec_cval hst2 h2', hcv2]
  have hpd3 : pdec (cdec (cdec (cdec c))) = pdec c := by rw [pdec_cdec hst2 h2', hpd2]
  -- the rule, the turn and the overflow
  have hsG : bstep b4_2LB ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .U :: .P1 :: tail⟩, 3) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_2LB) hst2 h2' (.U :: .P1 :: tail)
  have hsU : bstep b4_2LB ⟨cdec (cdec (cdec c)), .Rt, RB.U :: .P1 :: tail⟩
      = some (⟨cdec (cdec (cdec c)), .Lt, .Y :: .P1 :: tail⟩, 1) := rfl
  obtain ⟨k3, hr3⟩ :=
    brun_overflow_of (b4 := b4_2LB) hst3 hcv3 (.Y :: .P1 :: tail)
  rw [ofw_eq_pdec hst3 hcv3, hpd3] at hr3
  have hsL : bstep b4_2LB ⟨[LB.L], .Lt, pdec c ++ (RB.Y :: .P1 :: tail)⟩
      = some (⟨[LB.L], .Rt, .P2 :: (pdec c ++ (RB.Y :: .P1 :: tail))⟩, 4) := rfl
  -- the paid stack of the deposited word
  obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, -⟩ := paid_stack_facts hadm hg (two_le_unmatched hst hadm (by omega))
  set t : List LB := tfold [LB.L] (pdec c) with ht
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hbc : (3 : ℤ) ≤ bval c := by have := hg.head; omega
  -- the reset, with the residual `22` block as the last digit of the word
  have hwY : Digs (pdec c ++ [RB.Y]) :=
    (pdec_digs c).append (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Or.inl rfl)
  have hclY : 0 ≤ rrun (pdec c ++ [RB.Y]) (cval (paid true [LB.L])) := by
    simp only [paid_true]
    rw [show cval ([LB.L] : List LB) = 0 from rfl, Nat.cast_zero, rrun_append, hru]
    simp only [rrun_cons, rrun_nil, rstep_Y]
    omega
  obtain ⟨p', phys, k4, hrun4, hstp, hpaidp, hcvp⟩ :=
    brun_paid (b4 := b4_2LB) (pdec c ++ [RB.Y]) hwY true [LB.L] CStack.base
      (by simp) hclY (.P1 :: tail)
  have hpaid' : paid p' phys = LB.Z :: t := by
    rw [hpaidp]
    simp only [paid_true, tfold_append, tfold_cons, tstep_Y, tfold_nil, ht]
  have happ : pdec c ++ (RB.Y :: .P1 :: tail) = (pdec c ++ [RB.Y]) ++ (RB.P1 :: tail) := by
    simp
  obtain ⟨k5, hrun5⟩ :=
    brun_pd_P1 (b4 := b4_2LB) hstp (fun hpf => by have := hcvp hpf; omega) tail
  rw [hpaid'] at hrun5
  refine Returns.of_run
    (hr0.trans (BRun.head hsG (hr2.trans (BRun.head hsU (hr3.trans (BRun.of_step hsL)))))) ?_
  rw [happ]
  refine Returns.of_run hrun4 (Returns.of_run hrun5 ?_)
  rw [htail]
  -- the counter below the final pop is odd, so the stack is good
  have hcvZ : cval (LB.Z :: t) = 2 * cval t + 1 := rfl
  have hodd : cval (LB.Z :: t) % 2 = 1 := by rw [hcvZ]; omega
  refine returns_Yrun hstt.consZ.consW
    (adm_consW (adm_consZ hadmt) (by have := hadmt.head; simp; omega))
    (good_consW_odd (good_consZ hgt) hodd) hr (Or.inr ?_)
  have hcv : (cval t : ℤ) = bval c := hcvt
  simp only [cval_W, hcvZ]
  omega

/-! ## The arithmetic of the exceptional checkpoint -/

/-- The numerical content of the exceptional checkpoint of `2LB`: if the stack
`W :: W :: t` is not good, then the counter of `t` is large and the two pops
still satisfy the bounds the repair needs. -/
private theorem exc_2LB_arith {f : ℕ} {B bW bK : ℤ}
    (hf : 4 ≤ f) (hB : (f : ℤ) ≤ B)
    (hbW : bW = if f % 2 = 1 then 2 * B else B / 2 - 1)
    (hbK : bK = if (f / 2) % 2 = 1 then 2 * bW else bW / 2 - 1)
    (hdic : (f : ℤ) % 2 = 1 ∨ 11 ≤ B)
    (hm4 : f % 4 = 0 → 43 ≤ B)
    (hnot : ¬ (((f / 2 : ℕ) : ℤ) ≤ bW ∧ ((f / 2 / 2 : ℕ) : ℤ) ≤ bK)) :
    4 ≤ f / 2 ∧ 0 ≤ bW ∧ 3 * ((f / 2 : ℕ) : ℤ) ≤ 4 * bW + 14 ∧
      2 ≤ f / 2 / 2 ∧ ((f / 2 / 2 : ℕ) : ℤ) - 2 ≤ bK ∧
      ((f / 2 / 2) % 2 = 0 → 3 * (((f / 2 / 2 : ℕ) : ℤ) / 2) ≤ 4 * (bK / 2)) := by
  rcases not_and_or.mp hnot with hno | hno
  · by_cases h2 : f % 2 = 1
    · rw [if_pos h2] at hbW
      by_cases h4 : (f / 2) % 2 = 1
      · rw [if_pos h4] at hbK; omega
      · rw [if_neg h4] at hbK; omega
    · rw [if_neg h2] at hbW
      have hB11 : 11 ≤ B := by rcases hdic with h | h; · omega
                               · exact h
      by_cases h4 : (f / 2) % 2 = 1
      · rw [if_pos h4] at hbK; omega
      · rw [if_neg h4] at hbK
        have h43 : 43 ≤ B := hm4 (by omega)
        omega
  · by_cases h2 : f % 2 = 1
    · rw [if_pos h2] at hbW
      by_cases h4 : (f / 2) % 2 = 1
      · rw [if_pos h4] at hbK; omega
      · rw [if_neg h4] at hbK; omega
    · rw [if_neg h2] at hbW
      have hB11 : 11 ≤ B := by rcases hdic with h | h; · omega
                               · exact h
      by_cases h4 : (f / 2) % 2 = 1
      · rw [if_pos h4] at hbK; omega
      · rw [if_neg h4] at hbK
        have h43 : 43 ≤ B := hm4 (by omega)
        omega

/-! ## The exceptional checkpoint -/

/-- **The checkpoint stack `W :: W :: t` of the exceptional case.**  Two pops
in a row: the invariant can fail, but the machine still comes back to a safe
checkpoint. -/
private theorem returns_WWt {t : List LB} (hst : CStack t) (hadm : Adm t) (hg : Good t)
    (hf : 4 ≤ cval t) (hdic : (cval t : ℤ) % 2 = 1 ∨ 11 ≤ bval t)
    (hm4 : cval t % 4 = 0 → 43 ≤ bval t) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_2LB ⟨.W :: .W :: t, .Rt, List.replicate r .Y ++ [.R1]⟩ := by
  have hcount1 : 1 ≤ nbit t - nsh t := one_le_unmatched hst hadm (by omega)
  have hcount2 : 2 ≤ nbit t - nsh t := two_le_unmatched hst hadm (by omega)
  have hstW : CStack (LB.W :: t) := hst.consW
  have hadmW : Adm (LB.W :: t) := adm_consW hadm (by omega)
  have hstK : CStack (LB.W :: LB.W :: t) := hstW.consW
  have hadmK : Adm (LB.W :: LB.W :: t) := adm_consW hadmW (by simp; omega)
  have hcvW : cval (LB.W :: t) = cval t / 2 := rfl
  have hcvK : cval (LB.W :: LB.W :: t) = cval t / 2 / 2 := rfl
  have hbvW : bval (LB.W :: t) = if cval t % 2 = 1 then 2 * bval t else bval t / 2 - 1 := rfl
  have hbvK : bval (LB.W :: LB.W :: t)
      = if cval t / 2 % 2 = 1 then 2 * bval (LB.W :: t) else bval (LB.W :: t) / 2 - 1 := rfl
  by_cases hgood : ((cval t / 2 : ℕ) : ℤ) ≤ bval (LB.W :: t) ∧
      ((cval t / 2 / 2 : ℕ) : ℤ) ≤ bval (LB.W :: LB.W :: t)
  · -- the stack is good after all
    have hgW : Good (LB.W :: t) := hg.cons (by rw [hcvW]; exact hgood.1)
    have hgK : Good (LB.W :: LB.W :: t) := hgW.cons (by rw [hcvK]; exact hgood.2)
    refine returns_Yrun hstK hadmK hgK hr (Or.inr ?_)
    rw [hcvK]
    omega
  · -- the genuinely exceptional case
    obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩ :=
      exc_2LB_arith hf (by have := hg.head; omega) hbvW hbvK hdic hm4 hgood
    obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    obtain ⟨k1, hrun1⟩ := brun_Yrun_cp (b4 := b4_2LB) hstK (r := j + 1) (by omega)
    refine Returns.of_run hrun1 ?_
    simp only [Nat.add_sub_cancel]
    refine Returns.of_run (brun_Bt_X (b4 := b4_2LB) _) ?_
    match j with
    | 0 =>
        -- the sweep meets the second pop straight away: the ordinary case
        simp only [List.replicate_zero, List.nil_append]
        refine Returns.of_run (brun_Bt_W (b4 := b4_2LB) _ _) ?_
        refine wcase_2LB_ord_weak hstW hadmW hk2 ?_ (by rw [hcvW]; omega) (by omega)
        rw [hcvW]
        omega
    | (i + 1) =>
        -- the sweep meets a bit block
        rw [List.replicate_succ, List.cons_append]
        refine Returns.of_run (brun_Bt_Z (b4 := b4_2LB) _ _) ?_
        set K : List LB := LB.W :: LB.W :: t with hK
        set H : List LB := List.replicate i LB.Z ++ K with hH
        have hstH : CStack H := CStack_Zrun _ hstK
        have hadmH : Adm H := Adm_Zrun _ hadmK
        have hcvH : cval H = 2 ^ i * (cval K + 1) - 1 := by rw [hH, cval_Zrun]
        have hbvH : bval H = 2 ^ i * (bval K + 1) - 1 := by rw [hH, bval_Zrun]
        have hA0 : 2 ≤ cval K := by rw [hcvK]; omega
        have hC0 : (cval K : ℤ) - 2 ≤ bval K := by rw [hcvK]; exact hk5
        have hPpos : 1 ≤ (2 : ℕ) ^ i := Nat.one_le_two_pow
        have hQ3 : 3 ≤ 2 ^ i * (cval K + 1) := by
          have : cval K + 1 ≤ 2 ^ i * (cval K + 1) :=
            Nat.le_mul_of_pos_left _ (by positivity)
          omega
        have hA2 : 2 ≤ cval H := by rw [hcvH]; omega
        have hcast : ((2 ^ i * (cval K + 1) : ℕ) : ℤ) = (2 : ℤ) ^ i * ((cval K : ℤ) + 1) := by
          push_cast; ring
        have hAZ : (cval H : ℤ) = (2 : ℤ) ^ i * ((cval K : ℤ) + 1) - 1 := by
          rw [hcvH]; omega
        have hCZ : bval H = (2 : ℤ) ^ i * (bval K + 1) - 1 := hbvH
        have hPZ : (1 : ℤ) ≤ (2 : ℤ) ^ i := one_le_pow₀ (by norm_num)
        obtain ⟨hcvW', hbvW'⟩ := values_W_cdec2 hstH hA2
        refine returns_dX_weak hstH hadmH hA2 ?_ (by omega)
        rw [hcvW', hbvW']
        by_cases hpar : (cval H - 2) % 2 = 1
        · -- the counter below the bit block is odd
          rw [if_pos hpar]
          have hbase : 3 * ((cval K : ℤ) + 1) + 2 ≤ 16 * (bval K + 1) := by omega
          have hscaled : 3 * ((2 : ℤ) ^ i * ((cval K : ℤ) + 1)) + 2 * (2 : ℤ) ^ i
              ≤ 16 * ((2 : ℤ) ^ i * (bval K + 1)) := by nlinarith
          have hnZ : 2 * (((cval H - 2) / 2 : ℕ) : ℤ) = (cval H : ℤ) - 3 := by
            have : 2 * ((cval H - 2) / 2) = cval H - 3 := by omega
            omega
          omega
        · -- the counter is even: this forces `i = 0`
          rw [if_neg hpar]
          have hi0 : i = 0 := by
            by_contra hne
            obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            have hu3 : 3 ≤ 2 ^ i' * (cval K + 1) := by
              have : cval K + 1 ≤ 2 ^ i' * (cval K + 1) :=
                Nat.le_mul_of_pos_left _ (by positivity)
              omega
            have hdouble : 2 ^ (i' + 1) * (cval K + 1) = 2 * (2 ^ i' * (cval K + 1)) := by
              rw [pow_succ]; ring
            rw [hdouble] at hcvH
            omega
          subst hi0
          simp only [pow_zero, one_mul] at hAZ hCZ hcvH
          have hKeven : cval K % 2 = 0 := by omega
          have hk6' := hk6 (by rw [← hcvK]; exact hKeven)
          rw [← hcvK] at hk6'
          have hnZ : 2 * (((cval H - 2) / 2 : ℕ) : ℤ) = (cval H : ℤ) - 2 := by
            have : 2 * ((cval H - 2) / 2) = cval H - 2 := by omega
            omega
          omega

/-! ## The exceptional case of the sweep -/

/-- **The `W` case of the sweep for `2LB`, with a counter of exactly two.**
The third decrement overflows, so the residual `12` block is crossed after the
reset: it pushes a pop, and the pending `1>` pushes a second one. -/
theorem wcase_2LB_exc {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : cval c = 2) (hb4 : 4 ≤ bval c) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_2LB ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  obtain ⟨k0, hr0⟩ := brun_to_G (b4 := b4_2LB) hst (by omega) tail
  have hst1 : CStack (cdec c) := cdec_CStack_all hst
  have hadm1 : Adm (cdec c) := Adm.cdec hst hadm h1
  have hcv1 : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hpd1 : pdec (cdec c) = pdec c := pdec_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hst2 : CStack (cdec (cdec c)) := cdec_CStack_all hst1
  have hadm2 : Adm (cdec (cdec c)) := Adm.cdec hst1 hadm1 h1'
  have hcv2 : cval (cdec (cdec c)) = 0 := by rw [cdec_cval hst1 h1', hcv1]; omega
  have hpd2 : pdec (cdec (cdec c)) = pdec c := by rw [pdec_cdec hst1 h1', hpd1]
  -- the rule and the overflow
  have hsG : bstep b4_2LB ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .U :: .P1 :: tail⟩, 3) := rfl
  obtain ⟨k2, hr2⟩ :=
    brun_overflow_of (b4 := b4_2LB) hst2 hcv2 (.U :: .P1 :: tail)
  rw [ofw_eq_pdec hst2 hcv2, hpd2] at hr2
  have hsL : bstep b4_2LB ⟨[LB.L], .Lt, pdec c ++ (RB.U :: .P1 :: tail)⟩
      = some (⟨[LB.L], .Rt, .P2 :: (pdec c ++ (RB.U :: .P1 :: tail))⟩, 4) := rfl
  -- the paid stack of the deposited word
  obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, hdic⟩ := paid_stack_facts hadm hg (two_le_unmatched hst hadm (by omega))
  have hm4 := paid_stack_mod_four hadm hg (two_le_unmatched hst hadm (by omega))
  set t : List LB := tfold [LB.L] (pdec c) with ht
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hclu : 0 ≤ rrun (pdec c) (cval (paid true [LB.L])) := by
    simp only [paid_true]
    rw [show cval ([LB.L] : List LB) = 0 from rfl, Nat.cast_zero, hru]
    omega
  obtain ⟨p', phys, k3, hrun3, hstp, hpaidp, hcvp⟩ :=
    brun_paid (b4 := b4_2LB) (pdec c) (pdec_digs c) true [LB.L] CStack.base
      (by simp) hclu (.U :: .P1 :: tail)
  have hpaid' : paid p' phys = t := by rw [hpaidp]; simp only [paid_true, ht]
  -- crossing the `12` block and then the pending digit
  obtain ⟨k4, hrun4⟩ :=
    brun_pd_U (b4 := b4_2LB) hstp (fun hpf => by have := hcvp hpf; omega) (.P1 :: tail)
  rw [hpaid'] at hrun4
  obtain ⟨k5, hrun5⟩ :=
    brun_pd_P1 (b4 := b4_2LB) (p := true) hstt.consW (by simp) tail
  simp only [paid_true] at hrun5
  refine Returns.of_run (hr0.trans (BRun.head hsG (hr2.trans (BRun.of_step hsL)))) ?_
  refine Returns.of_run hrun3 (Returns.of_run hrun4 (Returns.of_run hrun5 ?_))
  rw [htail]
  have hcv : (cval t : ℤ) = bval c := hcvt
  refine returns_WWt hstt hadmt hgt (by omega) ?_ ?_ hr
  · rcases hdic with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hmod
    exact hm4 (by omega)

/-! ## The `W` case for `2LB` -/

/-- **The `W` case of the `<B1` sweep for `2LB`.** -/
theorem wcase_2LB : WCase b4_2LB := by
  intro c r hst hadm hg hv hcrit _ hr2
  have hr : 1 ≤ r := by omega
  rcases (show cval c = 2 ∨ cval c = 3 ∨ 4 ≤ cval c by omega) with h2 | h3 | h4
  · exact wcase_2LB_exc hst hadm hg h2 (hcrit h2) hr
  · exact wcase_2LB_a3 hst hadm hg h3 hr
  · exact wcase_2LB_ord hst hadm hg h4 hr

end BB25.Prefix
