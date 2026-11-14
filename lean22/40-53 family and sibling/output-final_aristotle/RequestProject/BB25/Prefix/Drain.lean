/-
# The shared drain machinery of the return theorem

A **safe checkpoint** is a configuration `L s <B1 22 1$` whose left stack `s`
is a good admissible counter stack with a positive counter (`SafeCP`).

This file collects the parts of the return argument that do not depend on the
member-specific `A> 241` rule: the protected drain (`returns_strong`), the
pending-`2>` tail (`returns_tail`), the reset of a word deposited by an
overflow (`returns_overflow`), and the configuration `<A d 2> 22…1$` left
behind by a bit block of the `<B1` sweep (`returns_dP2`).

The invariant carried through the drain is *not* goodness of the stack but the
numerical bound

```
  3 * (cval σ + 1) ≤ bval σ + 2          (`Strong`, the entry of the drain)
  3 * (cval σ + 1) ≤ 4 * (bval σ + 1)    (the entry of a pending-`2>` tail)
```

which a good stack satisfies, but which also survives the exceptional
checkpoints of the members `0LA` and `2LB`, where goodness is lost for one
sweep.
-/
import RequestProject.BB25.Prefix.Reset
import RequestProject.BB25.Nonhalt

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Safe checkpoints -/

/-- A good, admissible counter stack with a positive counter, whose topmost
block is a zero bit.  The last condition — the checkpoint *ends in* `X`, in the
bottom-first reading — guarantees that the `<B1` sweep strips at least one zero
bit before it meets the block that decides the branch; the members treated in
`Marker.lean` need it. -/
structure SafeCP (s : List LB) : Prop where
  st : CStack s
  adm : Adm s
  good : Good s
  pos : 1 ≤ cval s
  endX : ∃ t, s = .X :: t

/-- The block configuration of a safe checkpoint. -/
def cpCfg (s : List LB) : BCfg := ⟨s, .Bt, [.Y, .R1]⟩

/-- From `c` the machine either reaches a safe checkpoint or never halts. -/
def Returns (b4 : Option (Sym × Dir × St)) (c : BCfg) : Prop :=
  (∃ s k, SafeCP s ∧ BRun b4 c (cpCfg s) k) ∨ ¬ Halts (M b4) c.den

theorem Returns.of_run {c c' : BCfg} {k : ℕ} (hr : BRun b4 c c' k) (h : Returns b4 c') :
    Returns b4 c := by
  rcases h with ⟨s, k', hs, hrun⟩ | hnh
  · exact Or.inl ⟨s, k + k', hs, hr.trans hrun⟩
  · exact Or.inr (hr.not_halts hnh)

theorem Returns.cp {s : List LB} (h : SafeCP s) : Returns b4 (cpCfg s) :=
  Or.inl ⟨s, 0, h, BRun.refl _⟩

/-! ## Runs of `22` blocks -/

theorem cval_Zrun (r : ℕ) (σ : List LB) :
    cval (List.replicate r .Z ++ σ) = 2 ^ r * (cval σ + 1) - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append, cval_Z, ih]
      have h1 : 1 ≤ 2 ^ r * (cval σ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : 2 ^ (r + 1) * (cval σ + 1) = 2 * (2 ^ r * (cval σ + 1)) := by ring
      rw [h2]
      omega

theorem bval_Zrun (r : ℕ) (σ : List LB) :
    bval (List.replicate r .Z ++ σ) = 2 ^ r * (bval σ + 1) - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append, bval_Z, ih, pow_succ]
      ring

theorem CStack_Zrun {σ : List LB} (r : ℕ) (h : CStack σ) :
    CStack (List.replicate r .Z ++ σ) := by
  induction r with
  | zero => simpa using h
  | succ r ih => rw [List.replicate_succ, List.cons_append]; exact ih.consZ

theorem Adm_Zrun {σ : List LB} (r : ℕ) (h : Adm σ) : Adm (List.replicate r .Z ++ σ) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append]
      refine ih.cons ?_
      have := ih.head
      simp
      omega

theorem Good_Zrun {σ : List LB} (r : ℕ) (h : Good σ) : Good (List.replicate r .Z ++ σ) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append]
      refine ih.cons ?_
      have := ih.head
      simp
      omega

theorem nbit_Zrun (r : ℕ) (σ : List LB) :
    nbit (List.replicate r .Z ++ σ) = nbit σ + r ∧
      nsh (List.replicate r .Z ++ σ) = nsh σ := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append]
      constructor
      · simp [ih.1]; omega
      · simp [ih.2]

/-- The head swallows a run of `22` blocks, one bit each. -/
theorem brun_Yrun (r : ℕ) (σ : List LB) (rest : List RB) :
    BRun b4 ⟨σ, .Rt, List.replicate r .Y ++ rest⟩
      ⟨List.replicate r .Z ++ σ, .Rt, rest⟩ (2 * r) := by
  induction r generalizing σ with
  | zero => simpa using BRun.refl (b4 := b4) _
  | succ r ih =>
      have h1 : bstep b4 ⟨σ, .Rt, RB.Y :: (List.replicate r RB.Y ++ rest)⟩
          = some (⟨.Z :: σ, .Rt, List.replicate r .Y ++ rest⟩, 2) := rfl
      have h2 := ih (.Z :: σ)
      have hrun := BRun.head (b4 := b4) h1 h2
      have he : List.replicate r LB.Z ++ (LB.Z :: σ) = List.replicate (r + 1) LB.Z ++ σ := by
        simp [List.replicate_succ', List.append_assoc]
      rw [he] at hrun
      rw [List.replicate_succ, List.cons_append]
      have hk : 2 + 2 * r = 2 * (r + 1) := by ring
      rwa [hk] at hrun

/-- The pending digit `2>` crosses a run of `22` blocks, one bit each. -/
theorem brun_P2_Yrun (r : ℕ) (σ : List LB) (rest : List RB) :
    BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ rest)⟩
      ⟨List.replicate r .Z ++ σ, .Rt, .P2 :: rest⟩ (2 * r) := by
  induction r generalizing σ with
  | zero => simpa using BRun.refl (b4 := b4) _
  | succ r ih =>
      have h1 : bstep b4 ⟨σ, .Rt, .P2 :: (RB.Y :: (List.replicate r RB.Y ++ rest))⟩
          = some (⟨σ, .Rt, .Y :: .P2 :: (List.replicate r .Y ++ rest)⟩, 0) := rfl
      have h2 : bstep b4 ⟨σ, .Rt, RB.Y :: .P2 :: (List.replicate r RB.Y ++ rest)⟩
          = some (⟨.Z :: σ, .Rt, .P2 :: (List.replicate r .Y ++ rest)⟩, 2) := rfl
      have h3 := ih (.Z :: σ)
      have hrun := BRun.head (b4 := b4) h1 (BRun.head (b4 := b4) h2 h3)
      have he : List.replicate r LB.Z ++ (LB.Z :: σ) = List.replicate (r + 1) LB.Z ++ σ := by
        simp [List.replicate_succ', List.append_assoc]
      rw [he] at hrun
      rw [List.replicate_succ, List.cons_append]
      have hk : 0 + (2 + 2 * r) = 2 * (r + 1) := by ring
      rwa [hk] at hrun

/-! ## The end of a reset phase -/

/-- The right end of the tape, reached with a pending digit: the machine enters
the `<B1` sweep with the paid stack. -/
theorem brun_end (p : Bool) (phys : List LB) (hst : CStack phys)
    (hp : p = false → 1 ≤ cval phys) :
    ∃ k, BRun b4 ⟨phys, .Rt, [pd p, .R]⟩ (cpCfg (paid p phys)) k := by
  cases p with
  | true =>
      refine ⟨0 + 11, ?_⟩
      exact BRun.head (show bstep b4 ⟨phys, .Rt, [.P2, .R]⟩ = some (⟨phys, .Rt, [.R2]⟩, 0) from rfl)
        (BRun.of_step (show bstep b4 ⟨phys, .Rt, [.R2]⟩
          = some (⟨phys, .Bt, [.Y, .R1]⟩, 11) from rfl))
  | false =>
      obtain ⟨k, hrun⟩ := brun_cdec_of (b4 := b4) hst (hp rfl) [.R2]
      refine ⟨0 + (1 + (k + 11)), ?_⟩
      exact BRun.head (show bstep b4 ⟨phys, .Rt, [.P1, .R]⟩ = some (⟨phys, .Rt, [.R1]⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, [.R1]⟩ = some (⟨phys, .Lt, [.R2]⟩, 1) from rfl)
          (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec phys, .Rt, [.R2]⟩
            = some (⟨cdec phys, .Bt, [.Y, .R1]⟩, 11) from rfl))))

/-! ## The empty counter stack -/

theorem adm_L : Adm [LB.L] := by
  intro t ht
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · simp
  · obtain rfl : t = [] := List.eq_nil_of_suffix_nil ht'
    simp

theorem good_L : Good [LB.L] := by
  intro t ht
  rcases List.suffix_cons_iff.mp ht with rfl | ht'
  · simp
  · obtain rfl : t = [] := List.eq_nil_of_suffix_nil ht'
    simp

/-! ## Pushing a pop -/

theorem good_consW {τ : List LB} (hg : Good τ) (h : (cval τ : ℤ) + 2 ≤ bval τ) :
    Good (.W :: τ) := by
  refine hg.cons ?_
  have h0 : (0 : ℤ) ≤ cval τ := Int.natCast_nonneg _
  by_cases hodd : cval τ % 2 = 1
  · simp only [cval_W, bval_W, hodd, if_pos]
    omega
  · simp only [cval_W, bval_W, hodd, if_false]
    omega

theorem good_consW_odd {τ : List LB} (hg : Good τ) (hodd : cval τ % 2 = 1) :
    Good (.W :: τ) := by
  refine hg.cons ?_
  have h0 : (0 : ℤ) ≤ cval τ := Int.natCast_nonneg _
  have h1 := hg.head
  simp only [cval_W, bval_W, hodd, if_pos]
  omega

theorem good_consZ {τ : List LB} (hg : Good τ) : Good (.Z :: τ) := by
  refine hg.cons ?_
  have := hg.head
  simp
  omega

theorem good_consX {τ : List LB} (hg : Good τ) : Good (.X :: τ) := by
  refine hg.cons ?_
  have := hg.head
  simp
  omega

theorem adm_consZ {τ : List LB} (hadm : Adm τ) : Adm (.Z :: τ) :=
  hadm.cons (by have := hadm.head; simp; omega)

theorem adm_consX {τ : List LB} (hadm : Adm τ) : Adm (.X :: τ) :=
  hadm.cons (by have := hadm.head; simp; omega)

theorem adm_consW {τ : List LB} (hadm : Adm τ) (h : nsh τ + 1 ≤ nbit τ) : Adm (.W :: τ) :=
  hadm.cons (by simp; omega)

/-! ## The milestones of a return -/

/-- **A protected right end (`M1`).**  The counter stack is admissible and
satisfies the drain bound `3 (cval + 1) ≤ bval + 2`.  Goodness is *not*
required: only this numerical bound survives the drain. -/
structure Strong (σ : List LB) : Prop where
  st : CStack σ
  adm : Adm σ
  bound : 3 * ((cval σ : ℤ) + 1) ≤ bval σ + 2

/-- The drain of an exhausted counter: the overflow rebuilds a counter and the
machine reaches a safe checkpoint. -/
theorem returns_strong_zero {σ : List LB} (hst : CStack σ) (hv : cval σ = 0)
    (hb2 : (1 : ℤ) ≤ bval σ) : Returns b4 ⟨σ, .Rt, [.R]⟩ := by
  -- the overflow deposits the decoded word
  have hs1 : bstep b4 ⟨σ, .Rt, [.R]⟩ = some (⟨σ, .Lt, [.V, .R]⟩, 3) := rfl
  obtain ⟨k1, hr1⟩ := brun_overflow_of (b4 := b4) hst hv [.V, .R]
  rw [ofw_eq_pdec hst hv] at hr1
  have hs2 : bstep b4 ⟨[.L], .Lt, pdec σ ++ [.V, .R]⟩
      = some (⟨[.L], .Rt, .P2 :: (pdec σ ++ [.V, .R])⟩, 4) := rfl
  -- the reset word
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
  obtain ⟨hst', hadm', hg', hcv', _, _⟩ :=
    tfold_props w hwd (σ := [LB.L]) CStack.base adm_L good_L (by simpa using hcl)
  set π : List LB := tfold [LB.L] w with hπ
  have hpaid' : paid p' phys = π := by simpa using hpaid
  have hcvπ : (cval π : ℤ) = 2 * bval σ := by
    have : (cval π : ℤ) = rrun w (cval ([LB.L] : List LB)) := hcv'
    rw [this]
    have h0 : cval ([LB.L] : List LB) = 0 := rfl
    rw [h0]
    simpa using hrw
  obtain ⟨k2, hr2⟩ := brun_end (b4 := b4) p' phys hstp (by
    intro hpf
    have := hcvp hpf
    omega)
  rw [hpaid'] at hr2
  have hendX : ∃ t, π = LB.X :: t :=
    ⟨tfold [LB.L] (pdec σ), by rw [hπ, hw, tfold_append]; rfl⟩
  refine Or.inl ⟨π, 3 + (k1 + (4 + (k + k2))), ⟨hst', hadm', hg', ?_, hendX⟩, ?_⟩
  · omega
  · have happ : w ++ [RB.R] = pdec σ ++ [RB.V, RB.R] := by
      rw [hw, List.append_assoc]
      rfl
    have hrun' : BRun b4 ⟨[LB.L], .Rt, .P2 :: (pdec σ ++ [.V, .R])⟩
        ⟨phys, .Rt, pd p' :: [RB.R]⟩ k := by
      rw [← happ]
      exact hrun
    exact BRun.head hs1 (hr1.trans (BRun.head hs2 (hrun'.trans hr2)))

/-- **The protected drain.**  Each round of the drain halves the counter and,
because the bound is invariant under both of its branches, the counter reaches
zero with a decoded value of at least one. -/
private theorem returns_strong_aux : ∀ (n : ℕ) (σ : List LB), cval σ ≤ n → Strong σ →
    Returns b4 ⟨σ, .Rt, [.R]⟩ := by
  intro n
  induction n with
  | zero =>
      intro σ hn h
      have hv : cval σ = 0 := by omega
      refine returns_strong_zero h.st hv ?_
      have := h.bound
      rw [hv] at this
      simpa using by omega
  | succ n ih =>
      intro σ hn h
      rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
      · refine returns_strong_zero h.st h0 ?_
        have := h.bound
        rw [h0] at this
        simpa using by omega
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
        refine Returns.of_run
          (BRun.head hs1 (hr1.trans (BRun.of_step hs2)) :
            BRun b4 ⟨σ, .Rt, [.R]⟩ ⟨.W :: cdec σ, .Rt, [.R]⟩ (3 + (k1 + 2))) ?_
        refine ih (.W :: cdec σ) ?_ ⟨hstd.consW, adm_consW hadmd ?_, ?_⟩
        · simp only [cval_W, hcv]
          omega
        · rw [nbit_cdec, nsh_cdec]
          omega
        · simp only [cval_W, bval_W, hcv, hbv]
          by_cases hodd : (cval σ - 1) % 2 = 1
          · simp only [hodd, if_pos]
            omega
          · simp only [hodd, if_false]
            omega

theorem returns_strong {σ : List LB} (h : Strong σ) : Returns b4 ⟨σ, .Rt, [.R]⟩ :=
  returns_strong_aux (cval σ) σ (le_refl _) h

/-- A good stack satisfies the entry bound of a pending-`2>` tail. -/
theorem tail_bound_of_good {σ : List LB} (hg : Good σ) :
    3 * ((cval σ : ℤ) + 1) ≤ 4 * (bval σ + 1) := by
  have := hg.head
  have h0 : (0 : ℤ) ≤ cval σ := Int.natCast_nonneg _
  omega

/-- **The pending-`2>` tail.**  The pending digit swallows the run of `22`
blocks, the terminal `1` turns the head around and the last bit is popped; the
result is a protected right end.  A run of length zero is allowed as soon as
the counter is odd, because the bit it pops is then a one. -/
theorem returns_tail {σ : List LB} (hst : CStack σ) (hadm : Adm σ)
    (hb : 3 * ((cval σ : ℤ) + 1) ≤ 4 * (bval σ + 1))
    {r : ℕ} (hr : 1 ≤ r ∨ cval σ % 2 = 1) :
    Returns b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set π : List LB := List.replicate r LB.Z ++ σ with hπ
  have hstπ : CStack π := CStack_Zrun _ hst
  have hadmπ : Adm π := Adm_Zrun _ hadm
  obtain ⟨hcount1, hcount2⟩ := nbit_Zrun r σ
  set N : ℕ := 2 ^ r * (cval σ + 1) with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcπ : cval π = N - 1 := by rw [hπ, cval_Zrun, hN]
  set M : ℤ := 2 ^ r * (bval σ + 1) with hM
  have hbπ : bval π = M - 1 := by rw [hπ, bval_Zrun, hM]
  -- the popped bit is a one
  have hNeven : 2 ∣ N := by
    rcases hr with h | h
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    · exact Dvd.dvd.mul_left (by omega) _
  have hodd : cval π % 2 = 1 := by omega
  -- the two bounds
  have hNM : 3 * (N : ℤ) ≤ 4 * M := by
    have h2 : (0:ℤ) < 2 ^ r := by positivity
    have hNcast : (N : ℤ) = 2 ^ r * ((cval σ : ℤ) + 1) := by rw [hN]; push_cast; ring
    rw [hNcast, hM]
    calc 3 * (2 ^ r * ((cval σ : ℤ) + 1)) = 2 ^ r * (3 * ((cval σ : ℤ) + 1)) := by ring
      _ ≤ 2 ^ r * (4 * (bval σ + 1)) := by
          exact mul_le_mul_of_nonneg_left hb (le_of_lt h2)
      _ = 4 * (2 ^ r * (bval σ + 1)) := by ring
  -- the machine: the pending digit swallows the run and pops the last bit
  have hrun1 : BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩
      ⟨π, .Rt, .P2 :: [.R1]⟩ (2 * r) := brun_P2_Yrun _ _ _
  have hs1 : bstep b4 ⟨π, .Rt, [.P2, .R1]⟩ = some (⟨π, .Rt, [.V, .R]⟩, 0) := rfl
  have hs2 : bstep b4 ⟨π, .Rt, [.V, .R]⟩ = some (⟨.W :: π, .Rt, [.R]⟩, 2) := rfl
  have hrun : BRun b4 ⟨σ, .Rt, .P2 :: (List.replicate r .Y ++ [.R1])⟩
      ⟨.W :: π, .Rt, [.R]⟩ (2 * r + (0 + 2)) :=
    hrun1.trans (BRun.head hs1 (BRun.of_step hs2))
  refine Returns.of_run hrun (returns_strong ?_)
  -- the resulting configuration is strong
  have hcW : cval (.W :: π) = N / 2 - 1 := by
    simp only [cval_W, hcπ]
    omega
  have hbW : bval (.W :: π) = 2 * (M - 1) := by
    rw [bval_W, if_pos hodd, hbπ]
  refine ⟨hstπ.consW, adm_consW hadmπ ?_, ?_⟩
  · have h3 := hadm.head
    rw [hcount1, hcount2]
    rcases hr with h | h
    · omega
    · have h1 : 1 ≤ cval σ := by omega
      have := one_le_unmatched hst hadm h1
      omega
  · rw [hcW, hbW]
    have hcast : ((N / 2 - 1 : ℕ) : ℤ) = (N : ℤ) / 2 - 1 := by omega
    rw [hcast]
    omega

/-! ## A run of `22` blocks in front of the terminal `1` -/

/-- The head swallows a run of `22` blocks, turns at the right end
and reaches a safe checkpoint. -/
theorem returns_Yrun {π : List LB} (hst : CStack π) (hadm : Adm π) (hg : Good π)
    {q : ℕ} (hq : 1 ≤ q) (hpos : 2 ≤ q ∨ 1 ≤ cval π) :
    Returns b4 ⟨π, .Rt, List.replicate q .Y ++ [.R1]⟩ := by
  set ρ : List LB := List.replicate q .Z ++ π with hρ
  have hstρ : CStack ρ := CStack_Zrun _ hst
  have hadmρ : Adm ρ := Adm_Zrun _ hadm
  have hgρ : Good ρ := Good_Zrun _ hg
  have hpow : 2 ≤ 2 ^ q := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  have hcρ : cval ρ = 2 ^ q * (cval π + 1) - 1 := cval_Zrun _ _
  have hmul : 4 ≤ 2 ^ q * (cval π + 1) := by
    rcases hpos with h | h
    · have hpow' : 4 ≤ 2 ^ q := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) h
      exact le_trans hpow' (Nat.le_mul_of_pos_right _ (by omega))
    · calc (4 : ℕ) = 2 * 2 := by norm_num
        _ ≤ 2 ^ q * (cval π + 1) := Nat.mul_le_mul hpow (by omega)
  have h1 : 1 ≤ cval ρ := by omega
  have hrun1 : BRun b4 ⟨π, .Rt, List.replicate q .Y ++ [.R1]⟩ ⟨ρ, .Rt, [.R1]⟩ (2 * q) :=
    brun_Yrun q π [.R1]
  have hs1 : bstep b4 ⟨ρ, .Rt, [RB.R1]⟩ = some (⟨ρ, .Lt, [.R2]⟩, 1) := rfl
  obtain ⟨k, hrk⟩ := brun_cdec_of (b4 := b4) hstρ h1 [.R2]
  have hs2 : bstep b4 ⟨cdec ρ, .Rt, [RB.R2]⟩ = some (⟨cdec ρ, .Bt, [.Y, .R1]⟩, 11) := rfl
  refine Returns.of_run (hrun1.trans (BRun.head hs1 (hrk.trans (BRun.of_step hs2)))) ?_
  refine Returns.cp ⟨cdec_CStack_all hstρ, Adm.cdec hstρ hadmρ h1, Good.cdec hstρ hgρ h1, ?_, ?_⟩
  · rw [cdec_cval hstρ h1]
    omega
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    exact ⟨List.replicate q' .Z ++ π, by rw [hρ, List.replicate_succ, List.cons_append, cdec_Z]⟩

/-! ## Resetting a clean word deposited by an overflow -/

/-- The reset of a clean word followed by a pending digit and the tail. -/
theorem returns_reset_P2 {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0)
    (r : ℕ) (hpos : 1 ≤ r ∨ 1 ≤ rrun w 0) :
    Returns b4 ⟨[LB.L], .Rt, .P2 :: (w ++ (.P2 :: (List.replicate r .Y ++ [.R1])))⟩ := by
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
  have hcvπ' : (cval π : ℤ) = rrun w 0 := by rw [hcvπ, hL]; norm_num
  have hY : RB.Y :: tail = List.replicate (r + 1) RB.Y ++ [RB.R1] := by
    rw [htail, List.replicate_succ, List.cons_append]
  have hfin : Returns b4 ⟨π, .Rt, RB.Y :: tail⟩ := by
    rw [hY]
    refine returns_Yrun hstπ hadmπ hgπ (by omega) ?_
    rcases hpos with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine Returns.of_run (c' := ⟨phys, .Rt, pd p' :: (.P2 :: tail)⟩) hrun ?_
  cases p' with
  | true =>
      have hpe : phys = π := by simpa using hpaid'
      subst hpe
      exact Returns.of_run (BRun.of_step (show bstep b4 ⟨π, .Rt, .P2 :: .P2 :: tail⟩
        = some (⟨π, .Rt, .Y :: tail⟩, 0) from rfl)) hfin
  | false =>
      have hcv : cval phys = cval π + 1 := by simpa using hcvp rfl
      have hcd : cdec phys = π := by simpa using hpaid'
      obtain ⟨k', hrun'⟩ := brun_cdec_of (b4 := b4) hstp (by omega) (.Y :: tail)
      rw [hcd] at hrun'
      refine Returns.of_run (BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .P2 :: tail⟩
          = some (⟨phys, .Rt, .U :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: tail⟩
            = some (⟨phys, .Lt, .Y :: tail⟩, 1) from rfl) hrun')) hfin

/-- The reset of a clean word followed by a run of `22` blocks and the tail. -/
theorem returns_reset_Yrun {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0)
    {q : ℕ} (hq : 2 ≤ q) :
    Returns b4 ⟨[LB.L], .Rt, .P2 :: (w ++ (List.replicate q .Y ++ [.R1]))⟩ := by
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
  refine Returns.of_run (c' := ⟨phys, .Rt, pd p' :: (.Y :: tail)⟩) hrun ?_
  cases p' with
  | true =>
      have hpe : phys = π := by simpa using hpaid'
      subst hpe
      have hY : RB.Y :: tail = List.replicate (m + 1) RB.Y ++ [RB.R1] := hsplit.symm
      rw [hY]
      exact returns_tail hstπ hadmπ (tail_bound_of_good hgπ) (Or.inl (by omega))
  | false =>
      have hcv : cval phys = cval π + 1 := by simpa using hcvp rfl
      have hcd : cdec phys = π := by simpa using hpaid'
      obtain ⟨k', hrun'⟩ := brun_cdec_of (b4 := b4) hstp (by omega)
        (.Y :: .P2 :: (List.replicate m RB.Y ++ [RB.R1]))
      rw [hcd] at hrun'
      refine Returns.of_run (BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .Y :: tail⟩
          = some (⟨phys, .Rt, .U :: .P2 :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: .P2 :: tail⟩
            = some (⟨phys, .Lt, .Y :: .P2 :: tail⟩, 1) from rfl)
          (hrun'.trans (BRun.of_step (show bstep b4 ⟨π, .Rt, .Y :: .P2 :: tail⟩
            = some (⟨.Z :: π, .Rt, .P2 :: tail⟩, 2) from rfl))))) ?_
      exact returns_tail hstπ.consZ (adm_consZ hadmπ)
        (tail_bound_of_good (good_consZ hgπ)) (Or.inl (by omega))

/-! ## The left-end spinout -/

/-- The spun-out configuration: the head sits at the left end in state `A` in
front of `1 1 2 2`. -/
def xyCfg (t : List Sym) : Cfg := ⟨[1, 1], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩

/-- Nine base steps insert one more `2`; no rule of the head `B4` is used. -/
theorem xy_spinout_step (t : List Sym) :
    steps (M b4) 9 (xyCfg t) = some (xyCfg (2 :: t)) := rfl

theorem xy_spinout_iter (t : List Sym) : ∀ j : ℕ,
    steps (M b4) (9 * j) (xyCfg t) = some (xyCfg (List.replicate j 2 ++ t)) := by
  intro j
  induction j with
  | zero => simp [steps]
  | succ j ih =>
      have hs := xy_spinout_step (b4 := b4) (List.replicate j 2 ++ t)
      have hr := steps_trans ih hs
      simpa [Nat.mul_add, Nat.mul_one, List.replicate_succ] using hr

theorem not_halts_xy (t : List Sym) : ¬ Halts (M b4) (xyCfg t) := by
  rintro ⟨n, hn⟩
  exact not_halts_within (xy_spinout_iter (b4 := b4) t n) n (by omega) hn

/-- An overflow into the bottom of an empty counter stack, with a `11` block
left over, is the spinout. -/
theorem not_halts_overflow_left (rest : List RB) :
    ¬ Halts (M b4) (BCfg.den ⟨[LB.L], .Lt, .X :: .P2 :: .Y :: rest⟩) := by
  have he : (BCfg.den ⟨[LB.L], .Lt, RB.X :: .P2 :: .Y :: rest⟩)
      = xyCfg (2 :: denR rest) := rfl
  rw [he]
  exact not_halts_xy _

/-- **The early overflow (`M3`).**  The head is about to sweep left into an
exhausted counter, with one residual digit and the tail in front of it. -/
theorem returns_overflow {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hB0 : 0 ≤ bval σ)
    (hv : cval σ = 0) {d : RB} (hd : d = RB.X ∨ d = RB.V ∨ d = RB.Y)
    {r : ℕ} (hr : 1 ≤ r ∨ d = RB.Y) :
    Returns b4 ⟨σ, .Lt, d :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have hru : rrun (pdec σ) 0 = bval σ := (bval_eq_rrun σ).symm
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hst hv (d :: .P2 :: tail)
  rw [ofw_eq_pdec hst hv] at hr0
  by_cases hclean : 0 ≤ rstep d (bval σ)
  · -- the whole reset word `pdec σ ++ [d]` is clean
    have hdig : Dig d := by
      rcases hd with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
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
    refine Returns.of_run (hr0.trans (BRun.of_step
      (show bstep b4 ⟨[LB.L], .Lt, (pdec σ ++ [d]) ++ (.P2 :: tail)⟩
        = some (⟨[LB.L], .Rt, .P2 :: ((pdec σ ++ [d]) ++ (.P2 :: tail))⟩, 4) from rfl))) ?_
    rw [htail]
    refine returns_reset_P2 hw hcl r ?_
    rcases hr with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [rrun_append, hru]
      subst h
      simp only [rrun_cons, rrun_nil, rstep_Y]
      omega
  · -- the exceptional case: the residual digit is a `11` block and the decoded
    -- value of the stack is `0` or `1`
    have hdX : d = RB.X := by
      rcases hd with h | h | h
      · exact h
      · rw [h] at hclean
        exact absurd (by simpa using (by omega : (0:ℤ) ≤ 2 * bval σ)) hclean
      · rw [h] at hclean
        exact absurd (by simpa using (by omega : (0:ℤ) ≤ 2 * bval σ + 1)) hclean
    subst hdX
    have hB1 : bval σ ≤ 1 := by
      simp only [rstep_X] at hclean
      omega
    -- the residual digit is a `11` block, so the run of `22` blocks is nonempty
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := by
      rcases hr with h | h
      · exact ⟨r - 1, by omega⟩
      · exact absurd h (by simp)
    have hsplit : tail = RB.Y :: (List.replicate m RB.Y ++ [RB.R1]) := by
      rw [htail, List.replicate_succ, List.cons_append]
    rcases eq_or_ne (pdec σ) [] with hu0 | hune
    · -- the stack is empty: the head falls into the left-end spinout
      refine Or.inr ?_
      rw [hu0] at hr0
      simp only [List.nil_append] at hr0
      refine hr0.not_halts ?_
      rw [hsplit]
      exact not_halts_overflow_left _
    · -- reset the decoded word, consume the `11` block and overflow once more
      have hwu : Digs (pdec σ) := pdec_digs σ
      have hdu : DyckPre (pdec σ) := pdec_dyck hadm
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
      -- the head crosses the `11` block and pushes a pop
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
      -- the new pop exhausts the counter but keeps the decoded value nonnegative
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
      have hfin : Returns b4 ⟨[LB.L], .Rt, .P2 :: (pdec (.W :: t) ++ (RB.Y :: tail))⟩ := by
        rw [hYtail]
        exact returns_reset_Yrun (pdec_digs _) hclW (by omega)
      refine Returns.of_run (hr0.trans (BRun.of_step (show bstep b4
          ⟨[LB.L], .Lt, pdec σ ++ (RB.X :: .P2 :: tail)⟩
          = some (⟨[LB.L], .Rt, .P2 :: (pdec σ ++ (RB.X :: .P2 :: tail))⟩, 4) from rfl))) ?_
      refine Returns.of_run hrun₁ (Returns.of_run hrun₂ ?_)
      refine Returns.of_run (BRun.head (show bstep b4 ⟨.W :: t, .Rt, .P1 :: .P2 :: tail⟩
          = some (⟨.W :: t, .Rt, .U :: tail⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨.W :: t, .Rt, .U :: tail⟩
            = some (⟨.W :: t, .Lt, .Y :: tail⟩, 1) from rfl) hrun₃)) ?_
      exact Returns.of_run (BRun.of_step (show bstep b4
        ⟨[LB.L], .Lt, pdec (.W :: t) ++ (RB.Y :: tail)⟩
        = some (⟨[LB.L], .Rt, .P2 :: (pdec (.W :: t) ++ (RB.Y :: tail))⟩, 4) from rfl)) hfin

/-- **The bit-and-pending-digit configuration.**  This is what both the `01`
block of the `<B1` sweep and the `241` rule of the two members produce. -/
theorem returns_dP2 {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    {d : RB} (hd : d = RB.X ∨ d = RB.Y) {r : ℕ} (hr : 1 ≤ r ∨ d = RB.Y) :
    Returns b4 ⟨σ, .Lt, d :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
  · have hd' : d = RB.X ∨ d = RB.V ∨ d = RB.Y := by
      rcases hd with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    have hB0 : 0 ≤ bval σ := by
      have h := hg.head
      rw [h0] at h
      simpa using h
    exact returns_overflow hst hadm hB0 h0 hd' hr
  · have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
    have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
    have hstd : CStack (cdec σ) := cdec_CStack_all hst
    have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
    have hgd : Good (cdec σ) := Good.cdec hst hg h1
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (d :: .P2 :: tail)
    rcases hd with rfl | rfl
    · -- the residual digit is a `11` block: the head turns once more
      have hr1' : 1 ≤ r := by
        rcases hr with h | h
        · exact h
        · exact absurd h (by simp)
      have hs1 : bstep b4 ⟨cdec σ, .Rt, .X :: .P2 :: tail⟩
          = some (⟨cdec σ, .Lt, .V :: .P2 :: tail⟩, 1) := rfl
      refine Returns.of_run (hr1.trans (BRun.of_step hs1)) ?_
      rcases Nat.eq_zero_or_pos (cval (cdec σ)) with h0' | h1'
      · have hB0 : 0 ≤ bval (cdec σ) := by
          have h := hgd.head
          rw [h0'] at h
          simpa using h
        exact returns_overflow hstd hadmd hB0 h0' (Or.inr (Or.inl rfl)) (Or.inl hr1')
      · have hcv2 : cval (cdec (cdec σ)) = cval (cdec σ) - 1 := cdec_cval hstd h1'
        have hbv2 : bval (cdec (cdec σ)) = bval (cdec σ) := bval_cdec hstd h1'
        have hstd2 : CStack (cdec (cdec σ)) := cdec_CStack_all hstd
        have hadmd2 : Adm (cdec (cdec σ)) := Adm.cdec hstd hadmd h1'
        have hgd2 : Good (cdec (cdec σ)) := Good.cdec hstd hgd h1'
        obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P2 :: tail)
        have hs2 : bstep b4 ⟨cdec (cdec σ), .Rt, .V :: .P2 :: tail⟩
            = some (⟨.W :: cdec (cdec σ), .Rt, .P2 :: tail⟩, 2) := rfl
        refine Returns.of_run (hr2.trans (BRun.of_step hs2)) ?_
        have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched hst hadm h1
        have hgh : (cval σ : ℤ) ≤ bval σ := hg.head
        refine returns_tail hstd2.consW (adm_consW hadmd2 ?_)
          (tail_bound_of_good (good_consW hgd2 ?_)) (Or.inl hr1')
        · rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
          omega
        · rw [hcv2, hcv, hbv2, hbv]
          omega
    · -- the residual digit is a `22` block: the head pushes a bit
      have hs1 : bstep b4 ⟨cdec σ, .Rt, .Y :: .P2 :: tail⟩
          = some (⟨.Z :: cdec σ, .Rt, .P2 :: tail⟩, 2) := rfl
      refine Returns.of_run (hr1.trans (BRun.of_step hs1)) ?_
      exact returns_tail hstd.consZ (adm_consZ hadmd)
        (tail_bound_of_good (good_consZ hgd)) (Or.inr (by simp))

/-- **A `22` block in front of a pending `2>`.**  Whatever the counter, the
head comes back to a safe checkpoint: a positive counter pushes a one bit, an
exhausted one overflows and resets. -/
theorem returns_YP2 {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ) (r : ℕ) :
    Returns b4 ⟨σ, .Lt, .Y :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
  · have hB0 : 0 ≤ bval σ := by
      have h := hg.head
      rw [h0] at h
      simpa using h
    exact returns_overflow hst hadm hB0 h0 (Or.inr (Or.inr rfl)) (Or.inr rfl)
  · have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
    have hstd : CStack (cdec σ) := cdec_CStack_all hst
    have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
    have hgd : Good (cdec σ) := Good.cdec hst hg h1
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.Y :: .P2 :: tail)
    have hs1 : bstep b4 ⟨cdec σ, .Rt, .Y :: .P2 :: tail⟩
        = some (⟨.Z :: cdec σ, .Rt, .P2 :: tail⟩, 2) := rfl
    refine Returns.of_run (hr1.trans (BRun.of_step hs1)) ?_
    exact returns_tail hstd.consZ (adm_consZ hadmd)
      (tail_bound_of_good (good_consZ hgd)) (Or.inr (by simp))

/-- **A pending `1>` in front of the tail.**  The pending digit and the first
`22` block re-parse to a `12` block and a pending `2>`; crossing the `12` turns
the head around, which pays the debt of the pending `1>`. -/
theorem returns_P1_tail {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    {r : ℕ} (hr : 1 ≤ r) :
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
  exact returns_YP2 hst hadm hg m

/-! ## The bit block of the sweep, without goodness -/

/-- The counter and the decoded value after the two decrements and the pop. -/
theorem values_W_cdec2 {σ : List LB} (hst : CStack σ) (h2 : 2 ≤ cval σ) :
    cval (LB.W :: cdec (cdec σ)) = (cval σ - 2) / 2 ∧
      bval (LB.W :: cdec (cdec σ)) =
        if (cval σ - 2) % 2 = 1 then 2 * bval σ else bval σ / 2 - 1 := by
  have h1 : 1 ≤ cval σ := by omega
  have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
  have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
  have hstd : CStack (cdec σ) := cdec_CStack_all hst
  have h1' : 1 ≤ cval (cdec σ) := by omega
  have hcv2 : cval (cdec (cdec σ)) = cval σ - 2 := by
    rw [cdec_cval hstd h1', hcv]
    omega
  have hbv2 : bval (cdec (cdec σ)) = bval σ := by
    rw [bval_cdec hstd h1', hbv]
  refine ⟨by rw [cval_W, hcv2], ?_⟩
  rw [bval_W, hcv2, hbv2]

/-- **The bit block of the `<B1` sweep, with no goodness assumption.**  Two
decrements and a pop lead into a pending-`2>` tail; all that is needed is the
numerical bound the resulting stack satisfies. -/
theorem returns_dX_weak {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (h2 : 2 ≤ cval σ)
    (hb : 3 * ((cval (LB.W :: cdec (cdec σ)) : ℤ) + 1)
      ≤ 4 * (bval (LB.W :: cdec (cdec σ)) + 1))
    {r : ℕ} (hr : 1 ≤ r) :
    Returns b4 ⟨σ, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ := by
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval σ := by omega
  have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
  have hstd : CStack (cdec σ) := cdec_CStack_all hst
  have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
  have h1' : 1 ≤ cval (cdec σ) := by omega
  have hstd2 : CStack (cdec (cdec σ)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec σ)) := Adm.cdec hstd hadmd h1'
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.X :: .P2 :: tail)
  have hs1 : bstep b4 ⟨cdec σ, .Rt, .X :: .P2 :: tail⟩
      = some (⟨cdec σ, .Lt, .V :: .P2 :: tail⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P2 :: tail)
  have hs2 : bstep b4 ⟨cdec (cdec σ), .Rt, .V :: .P2 :: tail⟩
      = some (⟨.W :: cdec (cdec σ), .Rt, .P2 :: tail⟩, 2) := rfl
  refine Returns.of_run (hr1.trans (BRun.head hs1 (hr2.trans (BRun.of_step hs2)))) ?_
  have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched hst hadm h1
  have hh := hadm.head
  refine returns_tail hstd2.consW (adm_consW hadmd2 ?_) hb (Or.inl hr)
  rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
  omega

end BB25.Prefix
