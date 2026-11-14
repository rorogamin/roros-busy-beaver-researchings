/-
# The member `0LA`

Its `A> 241` rule is

```
  A> 241  ⟶  <A 2 1>          (five base steps)
```

so the `241` block is replaced by a residual `2` block and a pending `1>`, and
the head turns around.  The residual `2` block is swallowed by the counter
below it (it pushes a pop) and the pending `1>` then runs into the tail.

Two things can happen at the `W` case of the `<B1` sweep:

* the counter below the pop is at least three, so the three decrements the
  member needs are all available and the resulting stack is still good — this
  is `wcase_0LA_ord`;
* the counter is exactly two.  Then the third decrement overflows, the stack
  deposits its decoded word, and the head comes back over the **paid reset
  stack** `t` with the residual `2` block and the pending `1>` still in front
  of it.  The stack at the next checkpoint is `W :: X :: t`, whose decoded
  value is one *less* than its counter allows, so goodness can fail.  This is
  the exceptional checkpoint, treated in `returns_WXt`.

The exceptional checkpoint is repaired by looking one sweep further: the `<B1`
sweep over `X :: 1^{r-1} :: W :: X :: t` either meets a bit block (and then the
numerical bound of `returns_dX_weak` suffices) or comes straight back to the
ordinary case with the much larger counter `X :: t`.  The bit-block branch
needs `bval t ≥ 8` when the counter of `t` is even, which is exactly what the
dichotomy of `paid_stack_facts` provides.
-/
import RequestProject.BB25.Prefix.Except

namespace BB25.Prefix

open BB25

/-! ## The ordinary case: a counter of at least three -/

/-- **The `W` case of the sweep for `0LA`, with a counter of at least three.**
Three decrements are available, the residual `2` block pushes a pop and the
pending `1>` runs into the tail. -/
theorem wcase_0LA_ord {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : 3 ≤ cval c) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_0LA ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  obtain ⟨k0, hr0⟩ := brun_to_G (b4 := b4_0LA) hst (by omega) tail
  have hst1 : CStack (cdec c) := cdec_CStack_all hst
  have hadm1 : Adm (cdec c) := Adm.cdec hst hadm h1
  have hg1 : Good (cdec c) := Good.cdec hst hg h1
  have hcv1 : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hbv1 : bval (cdec c) = bval c := bval_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hst2 : CStack (cdec (cdec c)) := cdec_CStack_all hst1
  have hadm2 : Adm (cdec (cdec c)) := Adm.cdec hst1 hadm1 h1'
  have hg2 : Good (cdec (cdec c)) := Good.cdec hst1 hg1 h1'
  have hcv2 : cval (cdec (cdec c)) = cval c - 2 := by
    rw [cdec_cval hst1 h1', hcv1]; omega
  have hbv2 : bval (cdec (cdec c)) = bval c := by rw [bval_cdec hst1 h1', hbv1]
  have h2' : 1 ≤ cval (cdec (cdec c)) := by omega
  have hst3 : CStack (cdec (cdec (cdec c))) := cdec_CStack_all hst2
  have hadm3 : Adm (cdec (cdec (cdec c))) := Adm.cdec hst2 hadm2 h2'
  have hg3 : Good (cdec (cdec (cdec c))) := Good.cdec hst2 hg2 h2'
  have hcv3 : cval (cdec (cdec (cdec c))) = cval c - 3 := by
    rw [cdec_cval hst2 h2', hcv2]; omega
  have hbv3 : bval (cdec (cdec (cdec c))) = bval c := by rw [bval_cdec hst2 h2', hbv2]
  have hsG : bstep b4_0LA ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .V :: .P1 :: tail⟩, 5) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_0LA) hst2 h2' (.V :: .P1 :: tail)
  have hsV : bstep b4_0LA ⟨cdec (cdec (cdec c)), .Rt, RB.V :: .P1 :: tail⟩
      = some (⟨.W :: cdec (cdec (cdec c)), .Rt, .P1 :: tail⟩, 2) := rfl
  refine Returns.of_run (hr0.trans (BRun.head hsG (hr2.trans (BRun.of_step hsV)))) ?_
  rw [htail]
  refine returns_P1_tail hst3.consW (adm_consW hadm3 ?_) (good_consW hg3 ?_) hr
  · have hcount : 1 ≤ nbit c - nsh c := one_le_unmatched hst hadm h1
    have hh := hadm.head
    rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
    omega
  · have := hg.head
    rw [hcv3, hbv3]
    omega

/-! ## The exceptional checkpoint -/

/-- **The checkpoint stack `W :: X :: t` of the exceptional case.**  Its
decoded value is `bval t - 1`, one less than the counter `cval t` allows, so it
need not be good.  Nevertheless the machine comes back to a safe checkpoint. -/
private theorem returns_WXt {t : List LB} (hst : CStack t) (hadm : Adm t) (hg : Good t)
    (hf : 4 ≤ cval t) (hdic : (cval t : ℤ) % 2 = 1 ∨ 11 ≤ bval t) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_0LA ⟨.W :: .X :: t, .Rt, List.replicate r .Y ++ [.R1]⟩ := by
  have hstX : CStack (LB.X :: t) := hst.consX
  have hadmX : Adm (LB.X :: t) := adm_consX hadm
  have hgX : Good (LB.X :: t) := good_consX hg
  have hstK : CStack (LB.W :: LB.X :: t) := hstX.consW
  have hadmK : Adm (LB.W :: LB.X :: t) :=
    adm_consW hadmX (by have := hadm.head; simp; omega)
  have hcvK : cval (LB.W :: LB.X :: t) = cval t := by
    simp only [cval_W, cval_X]
    omega
  have hbvK : bval (LB.W :: LB.X :: t) = bval t - 1 := by
    have hpar : ¬ cval (LB.X :: t) % 2 = 1 := by simp only [cval_X]; omega
    rw [bval_W, if_neg hpar, bval_X]
    omega
  by_cases hgd : (cval t : ℤ) + 1 ≤ bval t
  · -- the stack is good after all
    have hgK : Good (LB.W :: LB.X :: t) :=
      good_consW hgX (by simp only [cval_X, bval_X, Nat.cast_mul]; push_cast; omega)
    exact returns_Yrun hstK hadmK hgK hr (Or.inr (by rw [hcvK]; omega))
  · -- the genuinely exceptional case: the decoded value equals the counter
    have hB : bval t = (cval t : ℤ) := by have := hg.head; omega
    obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    obtain ⟨k1, hrun1⟩ := brun_Yrun_cp (b4 := b4_0LA) hstK (r := j + 1) (by omega)
    refine Returns.of_run hrun1 ?_
    simp only [Nat.add_sub_cancel]
    refine Returns.of_run (brun_Bt_X (b4 := b4_0LA) _) ?_
    match j with
    | 0 =>
        -- the sweep meets the pop straight away, and the counter `X :: t` is
        -- large: this is the ordinary case again
        simp only [List.replicate_zero, List.nil_append]
        refine Returns.of_run (brun_Bt_W (b4 := b4_0LA) _ _) ?_
        exact wcase_0LA_ord hstX hadmX hgX (by simp only [cval_X]; omega) (by omega)
    | (i + 1) =>
        -- the sweep meets a bit block
        rw [List.replicate_succ, List.cons_append]
        refine Returns.of_run (brun_Bt_Z (b4 := b4_0LA) _ _) ?_
        set H : List LB := List.replicate i LB.Z ++ (LB.W :: LB.X :: t) with hH
        have hstH : CStack H := CStack_Zrun _ hstK
        have hadmH : Adm H := Adm_Zrun _ hadmK
        have hcvH : cval H = 2 ^ i * (cval t + 1) - 1 := by
          rw [hH, cval_Zrun, hcvK]
        have hbvH : bval H = 2 ^ i * (bval t - 1 + 1) - 1 := by
          rw [hH, bval_Zrun, hbvK]
        -- the arithmetic of the two values
        have hPpos : 1 ≤ (2 : ℕ) ^ i := Nat.one_le_two_pow
        have hQ5 : 5 ≤ 2 ^ i * (cval t + 1) := by
          have : cval t + 1 ≤ 2 ^ i * (cval t + 1) :=
            Nat.le_mul_of_pos_left _ (by positivity)
          omega
        have hA2 : 2 ≤ cval H := by rw [hcvH]; omega
        have hcast : ((2 ^ i * (cval t + 1) : ℕ) : ℤ)
            = (2 : ℤ) ^ i * (cval t : ℤ) + (2 : ℤ) ^ i := by push_cast; ring
        have hAZ : (cval H : ℤ) = (2 : ℤ) ^ i * (cval t : ℤ) + (2 : ℤ) ^ i - 1 := by
          rw [hcvH]; omega
        have hCZ : bval H = (2 : ℤ) ^ i * (cval t : ℤ) - 1 := by
          rw [hbvH, hB]; ring
        have hPZ : (1 : ℤ) ≤ (2 : ℤ) ^ i := one_le_pow₀ (by norm_num)
        have hxp : (4 : ℤ) * (2 : ℤ) ^ i ≤ (2 : ℤ) ^ i * (cval t : ℤ) := by
          have h2 : (4 : ℤ) ≤ (cval t : ℤ) := by exact_mod_cast hf
          nlinarith
        obtain ⟨hcvW, hbvW⟩ := values_W_cdec2 hstH hA2
        refine returns_dX_weak hstH hadmH hA2 ?_ (by omega)
        rw [hcvW, hbvW]
        by_cases hpar : (cval H - 2) % 2 = 1
        · -- the counter of the stack below the bit block is odd
          rw [if_pos hpar]
          have hn : ((cval H - 2) / 2 : ℕ) = (cval H - 3) / 2 := by omega
          have hnZ : 2 * (((cval H - 2) / 2 : ℕ) : ℤ) = (cval H : ℤ) - 3 := by
            have : 2 * ((cval H - 2) / 2) = cval H - 3 := by omega
            omega
          omega
        · -- the counter is even: this forces `i = 0` and an even `cval t`
          rw [if_neg hpar]
          have hi0 : i = 0 := by
            by_contra hne
            obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            have hu5 : 5 ≤ 2 ^ i' * (cval t + 1) := by
              have : cval t + 1 ≤ 2 ^ i' * (cval t + 1) :=
                Nat.le_mul_of_pos_left _ (by positivity)
              omega
            have hdouble : 2 ^ (i' + 1) * (cval t + 1) = 2 * (2 ^ i' * (cval t + 1)) := by
              rw [pow_succ]; ring
            rw [hdouble] at hcvH
            omega
          subst hi0
          simp only [pow_zero, one_mul] at hAZ hCZ hcvH
          have heven : cval t % 2 = 0 := by omega
          have hf11 : 11 ≤ (cval t : ℤ) := by
            rcases hdic with hodd | hbig
            · omega
            · omega
          have hnZ : 2 * (((cval H - 2) / 2 : ℕ) : ℤ) = (cval H : ℤ) - 2 := by
            have : 2 * ((cval H - 2) / 2) = cval H - 2 := by omega
            omega
          omega

/-! ## The exceptional case of the sweep -/

/-- **The `W` case of the sweep for `0LA`, with a counter of exactly two.**
The third decrement overflows: the stack deposits its decoded word, the reset
rebuilds the paid stack `t`, the residual `2` block pushes a bit, the pending
`1>` pushes the pop, and the machine arrives at the exceptional checkpoint
`W :: X :: t`. -/
theorem wcase_0LA_exc {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : cval c = 2) (hb4 : 4 ≤ bval c) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4_0LA ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  obtain ⟨k0, hr0⟩ := brun_to_G (b4 := b4_0LA) hst (by omega) tail
  have hst1 : CStack (cdec c) := cdec_CStack_all hst
  have hadm1 : Adm (cdec c) := Adm.cdec hst hadm h1
  have hg1 : Good (cdec c) := Good.cdec hst hg h1
  have hcv1 : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hbv1 : bval (cdec c) = bval c := bval_cdec hst h1
  have hpd1 : pdec (cdec c) = pdec c := pdec_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hst2 : CStack (cdec (cdec c)) := cdec_CStack_all hst1
  have hadm2 : Adm (cdec (cdec c)) := Adm.cdec hst1 hadm1 h1'
  have hcv2 : cval (cdec (cdec c)) = 0 := by rw [cdec_cval hst1 h1', hcv1]; omega
  have hbv2 : bval (cdec (cdec c)) = bval c := by rw [bval_cdec hst1 h1', hbv1]
  have hpd2 : pdec (cdec (cdec c)) = pdec c := by rw [pdec_cdec hst1 h1', hpd1]
  -- the rule of the member and the overflow
  have hsG : bstep b4_0LA ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .V :: .P1 :: tail⟩, 5) := rfl
  obtain ⟨k2, hr2⟩ :=
    brun_overflow_of (b4 := b4_0LA) hst2 hcv2 (.V :: .P1 :: tail)
  rw [ofw_eq_pdec hst2 hcv2, hpd2] at hr2
  have hsL : bstep b4_0LA ⟨[LB.L], .Lt, pdec c ++ (RB.V :: .P1 :: tail)⟩
      = some (⟨[LB.L], .Rt, .P2 :: (pdec c ++ (RB.V :: .P1 :: tail))⟩, 4) := rfl
  -- the paid stack of the deposited word
  obtain ⟨hstt, hadmt, hgt, hcvt, hbvt, hdic⟩ := paid_stack_facts hadm hg (two_le_unmatched hst hadm (by omega))
  set t : List LB := tfold [LB.L] (pdec c) with ht
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  -- the reset, with the residual `2` block as the last digit of the word
  have hwV : Digs (pdec c ++ [RB.V]) :=
    (pdec_digs c).append (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Or.inr (Or.inl rfl))
  have hclV : 0 ≤ rrun (pdec c ++ [RB.V]) (cval (paid true [LB.L])) := by
    simp only [paid_true]
    rw [show cval ([LB.L] : List LB) = 0 from rfl, Nat.cast_zero, rrun_append, hru]
    simp only [rrun_cons, rrun_nil, rstep_V]
    omega
  obtain ⟨p', phys, k3, hrun3, hstp, hpaidp, hcvp⟩ :=
    brun_paid (b4 := b4_0LA) (pdec c ++ [RB.V]) hwV true [LB.L] CStack.base
      (by simp) hclV (.P1 :: tail)
  have hpaid' : paid p' phys = LB.X :: t := by
    rw [hpaidp]
    simp only [paid_true, tfold_append, tfold_cons, tstep_V, tfold_nil, ht]
  have happ : pdec c ++ (RB.V :: .P1 :: tail) = (pdec c ++ [RB.V]) ++ (RB.P1 :: tail) := by
    simp
  -- crossing the pending digit
  obtain ⟨k4, hrun4⟩ :=
    brun_pd_P1 (b4 := b4_0LA) hstp (fun hpf => by have := hcvp hpf; omega) tail
  rw [hpaid'] at hrun4
  refine Returns.of_run (hr0.trans (BRun.head hsG (hr2.trans (BRun.of_step hsL)))) ?_
  rw [happ]
  refine Returns.of_run hrun3 (Returns.of_run hrun4 ?_)
  rw [htail]
  refine returns_WXt hstt hadmt hgt ?_ ?_ hr
  · have : (cval t : ℤ) = bval c := hcvt
    omega
  · rcases hdic with h | h
    · exact Or.inl h
    · exact Or.inr h

/-! ## The `W` case for `0LA` -/

/-- **The `W` case of the `<B1` sweep for `0LA`.** -/
theorem wcase_0LA : WCase b4_0LA := by
  intro c r hst hadm hg hv hcrit _ hr2
  have hr : 1 ≤ r := by omega
  rcases (show cval c = 2 ∨ 3 ≤ cval c by omega) with h2 | h3
  · exact wcase_0LA_exc hst hadm hg h2 (hcrit h2) hr
  · exact wcase_0LA_ord hst hadm hg h3 hr

end BB25.Prefix
