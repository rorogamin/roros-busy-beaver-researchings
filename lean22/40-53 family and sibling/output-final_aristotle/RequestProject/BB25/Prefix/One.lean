/-
# The member `1LB`

Its `A> 241` rule is

```
  A> 241  ⟶  <A 11 1>        (three base steps)
```

so the `241` block leaves a residual zero bit and a **pending `1>`** — one
decrement owed — and the head sweeps left into the stack below.  Three cases:

* the counter below the pop is at least four: two further decrements and a pop
  land in an ordinary pending-`1>` tail (`returns_P1_tail`);
* it is exactly three, or exactly two: the counter runs out during those
  decrements, the head overflows and the deposited word is reset.  The
  checkpoint the machine then reaches can fail the goodness invariant, but only
  by **one unit**, and only in a situation where the counter is provably large.

`repair_return` is the repair: a checkpoint whose decoded value is one less
than its counter still returns, because the numerical bound the drain needs
(`returns_dX_weak`) survives a deficit of one as soon as the counter is at
least three — and at least eight when it is even.  The two lower bounds that
rule out the small even counters are the expansion barriers of `Expand.lean`:
a decoded word of height at least two whose value is even has an expanding
close (value at least `11`), and if its value is `2 mod 8` and at least `4` it
has two of them (value at least `43`).
-/
import RequestProject.BB25.Prefix.Except

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The `2 mod 8` barrier -/

/-- **A decoded word of value `2 mod 8` and at least `4` has two expanding
closes**, hence a large transduced value. -/
theorem paid_stack_mod_eight {c : List LB} (hadm : Adm c) (hg : Good c)
    (hh : 2 ≤ nbit c - nsh c) (h4 : 4 ≤ bval c) (hm : bval c % 8 = 2) :
    43 ≤ bval (tfold [LB.L] (pdec c)) := by
  obtain ⟨-, -, -, -, hbvt, -⟩ := paid_stack_facts hadm hg hh
  have hb0 : (0 : ℤ) ≤ bval c := le_trans (Int.natCast_nonneg _) hg.head
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hbal : bal (pdec c) = ((nbit c - nsh c : ℕ) : ℤ) := by
    rw [bal_pdec]
    have := hadm.head
    omega
  have hq : 2 ≤ qcnt (pdec c) 0 := by
    by_contra hc
    rcases rrun_shape_le_one (pdec_digs c) (pdec_dyck hadm) (by rw [hru]; exact hb0)
      (by omega) hbal hh with hodd | ⟨e, he, hval⟩
    · rw [hru] at hodd; omega
    · rw [hru] at hval
      -- `2 ^ e - 2` is `2 mod 8` only for `e = 2`, where it is `2`
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · norm_num at hval; omega
      · have h8 : (8 : ℤ) ∣ 2 ^ (d + 2) := by
          obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          exact ⟨2 ^ d', by ring⟩
        omega
  have hbound := trun_ge_pow_q2 (pdec_digs c) (pdec_dyck hadm) hbal (le_refl (0 : ℤ)) hq
  have hpow : (4 : ℤ) ≤ 2 ^ (nbit c - nsh c) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (nbit c - nsh c) := pow_le_pow_right₀ (by norm_num) hh
  rw [hbvt]
  norm_num at hbound
  omega

/-! ## The one-unit deficit -/

/-- **The repair of a one-unit deficit.**  The checkpoint stack `Z^j K` need
not be good: a decoded value one below the counter still satisfies the bound
the drain needs, as soon as the counter of `K` is at least three, and at least
eight when it is even. -/
theorem repair_return {K : List LB} (hst : CStack K) (hadm : Adm K)
    (hA : 3 ≤ cval K) (hB : (cval K : ℤ) - 1 ≤ bval K)
    (hev : cval K % 2 = 0 → 8 ≤ cval K) (j : ℕ) :
    Returns b4 ⟨List.replicate j .Z ++ K, .Lt, .X :: .P2 :: (List.replicate 2 .Y ++ [.R1])⟩ := by
  set σ : List LB := List.replicate j .Z ++ K with hσ
  have hstσ : CStack σ := CStack_Zrun _ hst
  have hadmσ : Adm σ := Adm_Zrun _ hadm
  set x : ℕ := 2 ^ j * (cval K + 1) with hxdef
  set y : ℤ := 2 ^ j * (bval K + 1) with hydef
  have hcσ : cval σ = x - 1 := cval_Zrun _ _
  have hbσ : bval σ = y - 1 := bval_Zrun _ _
  have hP1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hPz : (1 : ℤ) ≤ 2 ^ j := by
    have h := hP1
    have : ((1 : ℕ) : ℤ) ≤ ((2 ^ j : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at this
    exact this
  have hx4 : 4 * 2 ^ j ≤ x := by
    rw [hxdef]
    calc 4 * 2 ^ j = 2 ^ j * 4 := by ring
      _ ≤ 2 ^ j * (cval K + 1) := Nat.mul_le_mul_left _ (by omega)
  have hxcast : (x : ℤ) = 2 ^ j * ((cval K : ℤ) + 1) := by rw [hxdef]; push_cast; ring
  have hx4z : 4 * (2 : ℤ) ^ j ≤ (x : ℤ) := by
    have : ((4 * 2 ^ j : ℕ) : ℤ) ≤ ((x : ℕ) : ℤ) := by exact_mod_cast hx4
    push_cast at this
    exact this
  have hyx : (x : ℤ) - 2 ^ j ≤ y := by
    have h0 : (0 : ℤ) ≤ 2 ^ j := by positivity
    have hmul : (2 : ℤ) ^ j * ((cval K : ℤ)) ≤ 2 ^ j * (bval K + 1) :=
      mul_le_mul_of_nonneg_left (by omega) h0
    rw [hxcast, hydef]
    linarith
  have h2 : 2 ≤ cval σ := by omega
  refine returns_dX_weak hstσ hadmσ h2 ?_ (by omega : 1 ≤ 2)
  obtain ⟨hc1, hb1⟩ := values_W_cdec2 hstσ h2
  rw [hc1, hb1]
  have hdiv : 2 * ((cval σ - 2) / 2) ≤ cval σ - 2 := Nat.mul_div_le _ 2
  have hdivcast : 2 * (((cval σ - 2) / 2 : ℕ) : ℤ) ≤ (cval σ : ℤ) - 2 := by
    have hcast : (2 * ((cval σ - 2) / 2 : ℕ) : ℤ) ≤ ((cval σ - 2 : ℕ) : ℤ) := by exact_mod_cast hdiv
    push_cast at hcast ⊢
    omega
  match j with
  | 0 =>
      simp only [pow_zero, one_mul] at hxdef hydef hxcast hx4z hyx hPz
      by_cases hodd : (cval σ - 2) % 2 = 1
      · rw [if_pos hodd]
        omega
      · rw [if_neg hodd]
        have hA8 : 8 ≤ cval K := hev (by omega)
        omega
  | (i + 1) =>
      have hPe : 2 ∣ 2 ^ (i + 1) := dvd_pow_self 2 (by omega)
      have hxe : x % 2 = 0 := by
        obtain ⟨t, ht⟩ := hPe
        have hx2 : x = 2 * (t * (cval K + 1)) := by rw [hxdef, ht]; ring
        omega
      have hodd : (cval σ - 2) % 2 = 1 := by omega
      rw [if_pos hodd]
      omega

/-! ## The tail of a repaired or good checkpoint -/

/-- The head is at `A>` in front of the tail, on a stack that is either good or
carries a one-unit deficit: in both cases the machine returns. -/
theorem returns_tail_or_repair {K : List LB} (hst : CStack K) (hadm : Adm K)
    (hK : Good K ∨ (3 ≤ cval K ∧ (cval K : ℤ) - 1 ≤ bval K ∧ (cval K % 2 = 0 → 8 ≤ cval K)))
    {r : ℕ} (hr : 2 ≤ r) :
    Returns b4 ⟨K, .Rt, List.replicate r .Y ++ [.R1]⟩ := by
  rcases hK with hg | ⟨hA, hB, hev⟩
  · exact returns_Yrun hst hadm hg (by omega) (Or.inl hr)
  · obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
    obtain ⟨k, hrun⟩ := brun_Yrun_cp (b4 := b4) hst (r := j + 2) (by omega)
    refine Returns.of_run hrun ?_
    have he : j + 2 - 1 = j + 1 := by omega
    rw [he]
    refine Returns.of_run (brun_Bt_X (b4 := b4) _) ?_
    have hsplit : List.replicate (j + 1) LB.Z ++ K = .Z :: (List.replicate j .Z ++ K) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hsplit]
    refine Returns.of_run (brun_Bt_Z (b4 := b4) _ _) ?_
    exact repair_return hst hadm hA hB hev j

/-! ## The overflow with a pending `1>` -/

/-- An exhausted counter with one residual digit and a pending `1>` in front of
the tail: the head overflows, the deposited word is reset, the pending digits
merge into a pop, and the resulting stack carries the tail. -/
theorem returns_overflow_P1 {σ : List LB} (hst : CStack σ)
    (hv : cval σ = 0) {d : RB} (hd : Dig d) (hcl : 0 ≤ rstep d (bval σ))
    {r : ℕ} (hr : 2 ≤ r)
    (hK : Good (.W :: tfold [LB.L] (pdec σ ++ [d])) ∨
      (3 ≤ cval (.W :: tfold [LB.L] (pdec σ ++ [d])) ∧
        (cval (.W :: tfold [LB.L] (pdec σ ++ [d])) : ℤ) - 1
          ≤ bval (.W :: tfold [LB.L] (pdec σ ++ [d])) ∧
        (cval (.W :: tfold [LB.L] (pdec σ ++ [d])) % 2 = 0 →
          8 ≤ cval (.W :: tfold [LB.L] (pdec σ ++ [d]))))) :
    Returns b4 ⟨σ, .Lt, d :: .P1 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  set w : List RB := pdec σ ++ [d] with hw
  have hwd : Digs w := (pdec_digs σ).append (by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hd)
  have hru : rrun (pdec σ) 0 = bval σ := (bval_eq_rrun σ).symm
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hclw : 0 ≤ rrun w (cval ([LB.L] : List LB)) := by
    rw [hL, hw, rrun_append]
    simpa [hru] using hcl
  -- the overflow
  obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hst hv (d :: .P1 :: tail)
  rw [ofw_eq_pdec hst hv] at hr0
  have happ : pdec σ ++ (d :: .P1 :: tail) = w ++ (.P1 :: tail) := by rw [hw]; simp
  rw [happ] at hr0
  refine Returns.of_run hr0 ?_
  refine Returns.of_run (c' := ⟨[LB.L], .Rt, .P2 :: (w ++ (.P1 :: tail))⟩) (BRun.of_step rfl) ?_
  -- the reset
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hwd true [LB.L] CStack.base (by simp) (by simpa using hclw)
      (.P1 :: tail)
  obtain ⟨hstν, hadmν, hgν, hcvν, -, hcntν⟩ :=
    tfold_props w hwd (σ := [LB.L]) CStack.base adm_L good_L (by simpa using hclw)
  set ν : List LB := tfold [LB.L] w with hν
  have hpaid' : paid p' phys = ν := by simpa using hpaid
  refine Returns.of_run hrun ?_
  -- the two pending digits merge into a pop
  obtain ⟨k2, hr2⟩ := brun_pd_P1 (b4 := b4) hstp (by
    intro hpf
    have := hcvp hpf
    omega) tail
  rw [hpaid'] at hr2
  refine Returns.of_run hr2 ?_
  have hadmW : Adm (.W :: ν) := adm_consW hadmν (by
    have := hcntν (by rw [hw]; simp)
    have := hadmν.head
    omega)
  exact returns_tail_or_repair hstν.consW hadmW hK hr

/-! ## The three cases of the sweep for `1LB` -/

section XP1

variable {c2 : List LB}

/-- The counter below the pop is at least four: two further decrements and a
pop reach an ordinary pending-`1>` tail. -/
theorem returns_XP1_big (hst : CStack c2) (hadm : Adm c2) (hg : Good c2)
    (h2 : 2 ≤ cval c2) {r : ℕ} (hr : 1 ≤ r) :
    Returns b4 ⟨c2, .Lt, .X :: .P1 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c2 := by omega
  have hcv : cval (cdec c2) = cval c2 - 1 := cdec_cval hst h1
  have hstd : CStack (cdec c2) := cdec_CStack_all hst
  have hadmd : Adm (cdec c2) := Adm.cdec hst hadm h1
  have hgd : Good (cdec c2) := Good.cdec hst hg h1
  have h1' : 1 ≤ cval (cdec c2) := by omega
  have hstd2 : CStack (cdec (cdec c2)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec c2)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec c2)) := Good.cdec hstd hgd h1'
  have hcv2 : cval (cdec (cdec c2)) = cval c2 - 2 := by rw [cdec_cval hstd h1', hcv]; omega
  have hbv2 : bval (cdec (cdec c2)) = bval c2 := by
    rw [bval_cdec hstd h1', bval_cdec hst h1]
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.X :: .P1 :: tail)
  refine Returns.of_run hr1 ?_
  refine Returns.of_run (c' := ⟨cdec c2, .Lt, .V :: .P1 :: tail⟩) (BRun.of_step rfl) ?_
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P1 :: tail)
  refine Returns.of_run hr2 ?_
  refine Returns.of_run (c' := ⟨.W :: cdec (cdec c2), .Rt, .P1 :: tail⟩) (BRun.of_step rfl) ?_
  have hcount : 1 ≤ nbit c2 - nsh c2 := one_le_unmatched hst hadm h1
  have hadmh := hadm.head
  refine returns_P1_tail hstd2.consW (adm_consW hadmd2 ?_) (good_consW hgd2 ?_) hr
  · rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]; omega
  · rw [hcv2, hbv2]
    have hgh := hg.head
    have hcast : ((cval c2 - 2 : ℕ) : ℤ) = (cval c2 : ℤ) - 2 := by omega
    rw [hcast]
    omega

/-- The counter below the pop is exactly three: one decrement empties it, the
head overflows and the deposited word, extended by the residual `21` block, is
reset. -/
theorem returns_XP1_one (hst : CStack c2) (hadm : Adm c2) (hg : Good c2)
    (hlow : (cval c2 : ℤ) + 2 ≤ bval c2) (hh : 2 ≤ nbit c2 - nsh c2)
    (h1 : cval c2 = 1) {r : ℕ} (hr : 2 ≤ r) :
    Returns b4 ⟨c2, .Lt, .X :: .P1 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have hv1 : 1 ≤ cval c2 := by omega
  have hstd : CStack (cdec c2) := cdec_CStack_all hst
  have hadmd : Adm (cdec c2) := Adm.cdec hst hadm hv1
  have hgd : Good (cdec c2) := Good.cdec hst hg hv1
  have hcvd : cval (cdec c2) = 0 := by rw [cdec_cval hst hv1, h1]
  have hbvd : bval (cdec c2) = bval c2 := bval_cdec hst hv1
  have hhd : 2 ≤ nbit (cdec c2) - nsh (cdec c2) := by rw [nbit_cdec, nsh_cdec]; exact hh
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst hv1 (.X :: .P1 :: tail)
  refine Returns.of_run hr1 ?_
  refine Returns.of_run (c' := ⟨cdec c2, .Lt, .V :: .P1 :: tail⟩) (BRun.of_step rfl) ?_
  -- the overflow deposits the decoded word, followed by the residual `21`
  obtain ⟨hstt, hadmt, hgt, hcvt, -, hdic⟩ := paid_stack_facts hadmd hgd hhd
  set t : List LB := tfold [LB.L] (pdec (cdec c2)) with ht
  have hν : tfold [LB.L] (pdec (cdec c2) ++ [RB.V]) = .X :: t := by rw [tfold_append]; rfl
  have hcvz : (cval t : ℤ) = bval c2 := by rw [hcvt, hbvd]
  have hgth := hgt.head
  have hA3 : 3 ≤ cval t := by
    have : (3 : ℤ) ≤ (cval t : ℤ) := by rw [hcvz]; omega
    exact_mod_cast this
  refine returns_overflow_P1 (b4 := b4) hstd hcvd (Or.inr (Or.inl rfl)) ?_ hr ?_
  · simp only [rstep_V, hbvd]
    omega
  · rw [hν]
    -- the values of the checkpoint stack `W X t`
    have hcvK : cval (LB.W :: LB.X :: t) = cval t := by simp only [cval_W, cval_X]; omega
    have hbvK : bval (LB.W :: LB.X :: t) = bval t - 1 := by
      simp only [bval_W, bval_X, cval_X]
      rw [if_neg (by omega)]
      have h0 : (0 : ℤ) ≤ bval t := le_trans (Int.natCast_nonneg _) hgth
      omega
    by_cases hstrict : (cval t : ℤ) + 1 ≤ bval t
    · refine Or.inl ((good_consX hgt).cons ?_)
      rw [hcvK, hbvK]
      omega
    · refine Or.inr ⟨by omega, by rw [hcvK, hbvK]; omega, ?_⟩
      intro hev
      rw [hcvK] at hev ⊢
      rcases hdic with hodd | h11
      · omega
      · omega

/-- The counter below the pop is exactly two: the head overflows at once, and
the residual `11` block is the last letter of the reset word. -/
theorem returns_XP1_zero (hst : CStack c2) (hadm : Adm c2) (hg : Good c2)
    (hcrit : 4 ≤ bval c2) (hh : 2 ≤ nbit c2 - nsh c2)
    (h0 : cval c2 = 0) {r : ℕ} (hr : 2 ≤ r) :
    Returns b4 ⟨c2, .Lt, .X :: .P1 :: (List.replicate r .Y ++ [.R1])⟩ := by
  obtain ⟨hstt, hadmt, hgt, hcvt, -, hdic⟩ := paid_stack_facts hadm hg hh
  set t : List LB := tfold [LB.L] (pdec c2) with ht
  have hν : tfold [LB.L] (pdec c2 ++ [RB.X]) = cdec (.W :: t) := by rw [tfold_append]; rfl
  set f : ℕ := cval t with hfdef
  have hfz : (f : ℤ) = bval c2 := hcvt
  have hf4 : 4 ≤ f := by omega
  have hgth : (f : ℤ) ≤ bval t := hgt.head
  have hWt1 : 1 ≤ cval (LB.W :: t) := by simp only [cval_W]; omega
  have hcvn : cval (cdec (LB.W :: t)) = f / 2 - 1 := by
    rw [cdec_cval hstt.consW hWt1]; simp only [cval_W]; rw [hfdef]
  have hbvn : bval (cdec (LB.W :: t)) = bval (LB.W :: t) := bval_cdec hstt.consW hWt1
  have hbvW : bval (LB.W :: t) = if f % 2 = 1 then 2 * bval t else bval t / 2 - 1 := by
    simp only [bval_W]; rw [hfdef]
  -- the paid stack of the reset word is good
  have hwd : Digs (pdec c2 ++ [RB.X]) := (pdec_digs c2).append (by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact Or.inr (Or.inr rfl))
  have hru : rrun (pdec c2) 0 = bval c2 := (bval_eq_rrun c2).symm
  have hclw : 0 ≤ rrun (pdec c2 ++ [RB.X]) (cval ([LB.L] : List LB)) := by
    have hL : cval ([LB.L] : List LB) = 0 := rfl
    rw [hL, rrun_append]
    simp only [Nat.cast_zero, hru, rrun_cons, rrun_nil, rstep_X]
    omega
  obtain ⟨-, -, hgν, -, -, -⟩ :=
    tfold_props (pdec c2 ++ [RB.X]) hwd (σ := [LB.L]) CStack.base adm_L good_L hclw
  rw [hν] at hgν
  have hgνh : (cval (cdec (LB.W :: t)) : ℤ) ≤ bval (cdec (LB.W :: t)) := hgν.head
  refine returns_overflow_P1 (b4 := b4) hst h0 (Or.inr (Or.inr rfl)) ?_ hr ?_
  · simp only [rstep_X]
    omega
  · rw [hν]
    set ν : List LB := cdec (LB.W :: t) with hνdef
    have hcvK : cval (LB.W :: ν) = cval ν / 2 := by simp only [cval_W]
    have hbvK : bval (LB.W :: ν) =
        if cval ν % 2 = 1 then 2 * bval ν else bval ν / 2 - 1 := by simp only [bval_W]
    by_cases hodd : cval ν % 2 = 1
    · refine Or.inl (hgν.cons ?_)
      rw [hcvK, hbvK, if_pos hodd]
      have : (cval ν : ℤ) / 2 ≤ (cval ν : ℤ) := by omega
      have hcast : ((cval ν / 2 : ℕ) : ℤ) ≤ (cval ν : ℤ) := by omega
      omega
    · by_cases hgood : (cval (LB.W :: ν) : ℤ) ≤ bval (LB.W :: ν)
      · exact Or.inl (hgν.cons hgood)
      · -- the one-unit deficit
        rw [hcvK, hbvK, if_neg hodd] at hgood ⊢
        have hcast : 2 * ((cval ν / 2 : ℕ) : ℤ) = (cval ν : ℤ) := by omega
        -- the counter is `f / 2 - 1`, which is even here, so `f` is `2 mod 4`
        have hfmod : f % 4 = 2 := by omega
        have hB : bval t ≤ (f : ℤ) + 3 := by
          rw [hbvn, hbvW, if_neg (by omega)] at hgood
          omega
        have h11 : 11 ≤ bval t := by
          rcases hdic with hoddt | h11
          · omega
          · exact h11
        have hq3 : 3 ≤ (cval ν / 2 : ℕ) := by
          rcases (by omega : f % 8 = 2 ∨ f % 8 = 6) with h8 | h8
          · have h43 : 43 ≤ bval t := paid_stack_mod_eight hadm hg hh (by omega) (by omega)
            omega
          · omega
        refine Or.inr ⟨hq3, by omega, ?_⟩
        intro hev
        have h8 : f % 8 = 2 := by omega
        have h43 : 43 ≤ bval t := paid_stack_mod_eight hadm hg hh (by omega) (by omega)
        omega

end XP1

/-! ## The `W` case of the sweep for `1LB` -/

theorem gStep_1LB (lt : List LB) (rest : List RB) :
    gStep b4_1LB lt rest = some (⟨lt, .Lt, .X :: .P1 :: rest⟩, 3) := rfl

/-- **The `W` case of the `<B1` sweep for `1LB`.** -/
theorem wcase_1LB : WCase b4_1LB := by
  intro c r hst hadm hg hv hcrit _ hr
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval c := by omega
  have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hadmd : Adm (cdec c) := Adm.cdec hst hadm h1
  have hgd : Good (cdec c) := Good.cdec hst hg h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hstd2 : CStack (cdec (cdec c)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec c)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec c)) := Good.cdec hstd hgd h1'
  have hcv2 : cval (cdec (cdec c)) = cval c - 2 := by rw [cdec_cval hstd h1', hcv]; omega
  have hbv2 : bval (cdec (cdec c)) = bval c := by
    rw [bval_cdec hstd h1', bval_cdec hst h1]
  have hh2 : 2 ≤ nbit (cdec (cdec c)) - nsh (cdec (cdec c)) := by
    rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
    exact two_le_unmatched hst hadm hv
  -- two decrements bring the head to the `241` block, and the rule fires
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_1LB) hst h1 (.F :: tail)
  have hsF : bstep b4_1LB ⟨cdec c, .Rt, .F :: tail⟩ = some (⟨cdec c, .Lt, .G :: tail⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_1LB) hstd h1' (.G :: tail)
  have hsG : bstep b4_1LB ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec c), .Lt, .X :: .P1 :: tail⟩, 3) := gStep_1LB _ _
  refine Returns.of_run (hr1.trans (BRun.head hsF (hr2.trans (BRun.of_step hsG)))) ?_
  have hgh : (cval c : ℤ) ≤ bval c := hg.head
  have hcast : ((cval c - 2 : ℕ) : ℤ) = (cval c : ℤ) - 2 := by omega
  rcases (by omega : 2 ≤ cval (cdec (cdec c)) ∨ cval (cdec (cdec c)) = 1 ∨
      cval (cdec (cdec c)) = 0) with h2 | h1c | h0c
  · exact returns_XP1_big hstd2 hadmd2 hgd2 h2 (by omega)
  · refine returns_XP1_one hstd2 hadmd2 hgd2 ?_ hh2 h1c hr
    rw [hcv2, hbv2, hcast]
    omega
  · refine returns_XP1_zero hstd2 hadmd2 hgd2 ?_ hh2 h0c hr
    rw [hbv2]
    exact hcrit (by omega)

end BB25.Prefix
