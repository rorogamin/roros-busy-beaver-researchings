/-
# The member `1RB`

Its `A> 241` rule is

```
  A> 241  ⟶  013 A>        (three base steps)
```

so the `241` block becomes the block `J1 = 013` on the left stack, and the head
carries on to the right.  When the head eventually comes back to it,

```
  J1 <A  ⟶  <A 11 2>       (five base steps)
```

the block disappears *without leaving a bit behind* and the head keeps going
left, with a `11` block and a pending `2>` in front of it.  So `J1` is a marker
like the `K1` of `0RA` and the `J` of `2RB` — the local counter the sweep
builds above it drains against it and overflows onto it (`marker_drain`) — but
the configuration it hands back is the *bit-and-pending-digit* configuration
`c <A 11 2> w`, over the stack `c` that was below the `141` block, with the
word `w` the overflow deposited in front of it.

Two things can then happen, and they are the two halves of this file.

* If the counter of `c` is at least two, the head pays the two decrements the
  `11` block and the pending digit ask for, pops, and the word `w` is re-parsed
  in the ordinary **reset phase** over the good stack `03 D²(c)`
  (`returns_j1_ord`).
* If the counter of `c` is zero or one, the decrements are unavailable: the
  head runs off the left end, the whole decoded word of `c` is reset first, and
  the two pending digits then *cancel*, so that `w` is read in the **counter
  phase** over the rebuilt stack (`returns_j1_small`).  The rebuilt counter is
  large — its value is the decoded value of `c`, which the margins of the
  checkpoint and the small-value barrier of `Except.lean` bound from below.

The three words `w` that the marker can deposit are handled by `returns_ct0`,
`returns_ct1` and `returns_ctk`; the last one, `kword n`, is a balanced word,
so reading it in the counter phase returns the counter to its initial value
while multiplying the decoded value by `2 ^ (2n+2)`.
-/
import RequestProject.BB25.Prefix.DrainWord
import RequestProject.BB25.Prefix.Except
import RequestProject.BB25.Prefix.Marker

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The two rules of `1RB` -/

/-- The `A> 241` rule of `1RB`. -/
theorem gStep_1RB (lt : List LB) (rest : List RB) :
    gStep b4_1RB lt rest = some (⟨.J1 :: lt, .Rt, rest⟩, 3) := rfl

/-- The marker rule: the block disappears and the head keeps going left. -/
theorem j1_step (c2 : List LB) (rt : List RB) :
    bstep b4 ⟨.J1 :: c2, .Lt, rt⟩ = some (⟨c2, .Lt, .X :: .P2 :: rt⟩, 5) := rfl

/-! ## Two pending digits cancel -/

/-- **The merge of two pending digits.**  The head resets the clean word `w`
over the good stack `π` and then meets a second pending `2>`: the two pending
digits cancel into a `22` block, which pushes one bit, and the rest of the tape
is read in the counter phase. -/
theorem returns_merge {π : List LB} (hst : CStack π)
    {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w (cval π)) {T : List RB}
    (hcont : Returns b4 ⟨.Z :: tfold π w, .Rt, T⟩) :
    Returns b4 ⟨π, .Rt, .P2 :: (w ++ (.P2 :: T))⟩ := by
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) w hw true π hst (by simp) (by simpa using hcl) (.P2 :: T)
  set s : List LB := tfold π w with hs
  have hpaid' : paid p' phys = s := by simpa using hpaid
  refine Returns.of_run hrun ?_
  cases p' with
  | true =>
      have hpe : phys = s := by simpa using hpaid'
      subst hpe
      refine Returns.of_run (BRun.head (show bstep b4 ⟨s, .Rt, .P2 :: .P2 :: T⟩
          = some (⟨s, .Rt, .Y :: T⟩, 0) from rfl)
        (BRun.of_step (show bstep b4 ⟨s, .Rt, .Y :: T⟩
          = some (⟨.Z :: s, .Rt, T⟩, 2) from rfl))) hcont
  | false =>
      have hcv : cval phys = cval s + 1 := by simpa using hcvp rfl
      have hcd : cdec phys = s := by simpa using hpaid'
      obtain ⟨k', hrun'⟩ := brun_cdec_of (b4 := b4) hstp (by omega) (.Y :: T)
      rw [hcd] at hrun'
      refine Returns.of_run (BRun.head (show bstep b4 ⟨phys, .Rt, .P1 :: .P2 :: T⟩
          = some (⟨phys, .Rt, .U :: T⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨phys, .Rt, .U :: T⟩
            = some (⟨phys, .Lt, .Y :: T⟩, 1) from rfl)
          (hrun'.trans (BRun.of_step (show bstep b4 ⟨s, .Rt, .Y :: T⟩
            = some (⟨.Z :: s, .Rt, T⟩, 2) from rfl))))) hcont

/-! ## The three words the marker can deposit, read in the counter phase -/

/-- The deposited word of a sweep that left no one bit above the marker. -/
theorem returns_ct0 {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    (hodd : cval σ % 2 = 1) (hb : 7 ≤ bval σ) :
    Returns b4 ⟨σ, .Rt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  have h1 : 1 ≤ cval σ := by omega
  have hcv : cval (cdec σ) = cval σ - 1 := cdec_cval hst h1
  have hbv : bval (cdec σ) = bval σ := bval_cdec hst h1
  have hstd : CStack (cdec σ) := cdec_CStack_all hst
  have hadmd : Adm (cdec σ) := Adm.cdec hst hadm h1
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 [.V, .P2, .Y, .Y, .R1]
  refine Returns.of_run (BRun.head
    (show bstep b4 ⟨σ, .Rt, [.X, .P2, .Y, .Y, .R1]⟩
      = some (⟨σ, .Lt, [.V, .P2, .Y, .Y, .R1]⟩, 1) from rfl)
    (hr1.trans (BRun.of_step
      (show bstep b4 ⟨cdec σ, .Rt, [.V, .P2, .Y, .Y, .R1]⟩
        = some (⟨.W :: cdec σ, .Rt, [.P2, .Y, .Y, .R1]⟩, 2) from rfl)))) ?_
  have he : ([.P2, .Y, .Y, .R1] : List RB) = .P2 :: (List.replicate 2 .Y ++ [.R1]) := rfl
  rw [he]
  have hcount : 1 ≤ nbit σ - nsh σ := one_le_unmatched hst hadm h1
  have hadmh := hadm.head
  refine returns_tail hstd.consW (adm_consW hadmd ?_) ?_ (Or.inl (by omega))
  · rw [nbit_cdec, nsh_cdec]
    omega
  · have hgh := hg.head
    simp only [cval_W, bval_W, hcv, hbv, if_neg (show ¬ (cval σ - 1) % 2 = 1 by omega)]
    omega

/-- The deposited word of a sweep that left one one bit above the marker. -/
theorem returns_ct1 {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ) :
    Returns b4 ⟨σ, .Rt, [.Y, .V, .P2, .Y, .Y, .R1]⟩ := by
  refine Returns.of_run (BRun.head
    (show bstep b4 ⟨σ, .Rt, [.Y, .V, .P2, .Y, .Y, .R1]⟩
      = some (⟨.Z :: σ, .Rt, [.V, .P2, .Y, .Y, .R1]⟩, 2) from rfl)
    (BRun.of_step (show bstep b4 ⟨.Z :: σ, .Rt, [.V, .P2, .Y, .Y, .R1]⟩
      = some (⟨.W :: .Z :: σ, .Rt, [.P2, .Y, .Y, .R1]⟩, 2) from rfl))) ?_
  have he : ([.P2, .Y, .Y, .R1] : List RB) = .P2 :: (List.replicate 2 .Y ++ [.R1]) := rfl
  rw [he]
  have hadmh := hadm.head
  refine returns_tail hst.consZ.consW (adm_consW (adm_consZ hadm) ?_) ?_ (Or.inl (by omega))
  · simp only [nbit_Z, nsh_Z]
    omega
  · have hgh := hg.head
    have h0 : (0 : ℤ) ≤ cval σ := Int.natCast_nonneg _
    simp only [cval_W, bval_W, cval_Z, bval_Z,
      if_pos (show (2 * cval σ + 1) % 2 = 1 by omega)]
    have hdiv : (2 * cval σ + 1) / 2 = cval σ := by omega
    rw [hdiv]
    omega

/-- A tower of pops over a counter of the form `2 ^ m * (u + 1) - 1`: every pop
closes a one bit, so the decoded value doubles at each of them. -/
theorem Wrun_facts : ∀ (m : ℕ) (τ : List LB) (u : ℕ), CStack τ → Adm τ →
    cval τ = 2 ^ m * (u + 1) - 1 → nsh τ + m ≤ nbit τ →
    CStack (List.replicate m .W ++ τ) ∧ Adm (List.replicate m .W ++ τ) ∧
      cval (List.replicate m .W ++ τ) = u ∧
      bval (List.replicate m .W ++ τ) = 2 ^ m * bval τ := by
  intro m
  induction m with
  | zero =>
      intro τ u hst hadm hcv _
      refine ⟨by simpa using hst, by simpa using hadm, ?_, ?_⟩
      · simpa using by simpa using hcv
      · simp
  | succ m ih =>
      intro τ u hst hadm hcv hcount
      set q : ℕ := 2 ^ m * (u + 1) with hq
      have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hcv' : cval τ = 2 * q - 1 := by
        rw [hcv, hq, pow_succ]
        ring_nf
      have hodd : cval τ % 2 = 1 := by omega
      have hWcv : cval (.W :: τ) = 2 ^ m * (u + 1) - 1 := by
        simp only [cval_W, hcv']
        omega
      have hWbv : bval (.W :: τ) = 2 * bval τ := by rw [bval_W, if_pos hodd]
      obtain ⟨h1, h2, h3, h4⟩ := ih (.W :: τ) u hst.consW
        (adm_consW hadm (by omega)) hWcv (by simp only [nsh_W, nbit_W]; omega)
      have hsplit : List.replicate (m + 1) LB.W ++ τ = List.replicate m .W ++ (.W :: τ) := by
        rw [List.replicate_succ']
        simp
      rw [hsplit]
      refine ⟨h1, h2, h3, ?_⟩
      rw [h4, hWbv, pow_succ]
      ring

/-- **The deposited word of a sweep that left at least two one bits above the
marker, read in the counter phase.**  The word `kword n` is balanced, so it
gives the counter back — after one decrement — and multiplies the decoded value
by `2 ^ (2n+2)`; the drain at the right end then reaches a checkpoint. -/
theorem returns_ctk {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ) (k : ℕ) :
    Returns b4 ⟨σ, .Rt, kword (k + 2) ++ [.R]⟩ := by
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  set A : ℕ := 2 ^ k with hAdef
  set M : ℕ := A * (cval σ + 1) with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set N : ℤ := (A : ℤ) * (bval σ + 1) with hN
  have hb0 : (0 : ℤ) ≤ bval σ := le_trans (Int.natCast_nonneg _) hg.head
  have hMN : (M : ℤ) ≤ N := by
    rw [hM, hN]
    have : (cval σ : ℤ) + 1 ≤ bval σ + 1 := by have := hg.head; omega
    push_cast
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- the word
  have hword : kword (k + 2) ++ [RB.R]
      = List.replicate (k + 2) .Y ++ (.V :: .Y :: .Y :: .V :: .X ::
          (List.replicate (k + 1) .V ++ [.R])) := by
    rw [kword]
    simp
  rw [hword]
  -- the stacks the counter phase builds
  set ρ₁ : List LB := List.replicate (k + 2) .Z ++ σ with hρ₁
  set ρ₂ : List LB := .W :: ρ₁ with hρ₂
  set ρ₃ : List LB := .Z :: ρ₂ with hρ₃
  set ρ₄ : List LB := .Z :: ρ₃ with hρ₄
  set ρ₅ : List LB := .W :: ρ₄ with hρ₅
  set ρ₆ : List LB := .W :: cdec ρ₅ with hρ₆
  -- their counters
  have hpow : (2 : ℕ) ^ (k + 2) = 4 * A := by rw [hAdef, pow_succ, pow_succ]; ring
  have hc₁ : cval ρ₁ = 4 * M - 1 := by
    rw [hρ₁, cval_Zrun, hpow, hM]
    ring_nf
  have hc₂ : cval ρ₂ = 2 * M - 1 := by simp only [hρ₂, cval_W, hc₁]; omega
  have hc₃ : cval ρ₃ = 4 * M - 1 := by simp only [hρ₃, cval_Z, hc₂]; omega
  have hc₄ : cval ρ₄ = 8 * M - 1 := by simp only [hρ₄, cval_Z, hc₃]; omega
  have hc₅ : cval ρ₅ = 4 * M - 1 := by simp only [hρ₅, cval_W, hc₄]; omega
  -- their stack structure
  have hst₁ : CStack ρ₁ := CStack_Zrun _ hst
  have hst₂ : CStack ρ₂ := hst₁.consW
  have hst₃ : CStack ρ₃ := hst₂.consZ
  have hst₄ : CStack ρ₄ := hst₃.consZ
  have hst₅ : CStack ρ₅ := hst₄.consW
  have hstd : CStack (cdec ρ₅) := cdec_CStack_all hst₅
  have hst₆ : CStack ρ₆ := hstd.consW
  have h5pos : 1 ≤ cval ρ₅ := by omega
  have hcd : cval (cdec ρ₅) = 4 * M - 2 := by rw [cdec_cval hst₅ h5pos, hc₅]; omega
  have hc₆ : cval ρ₆ = 2 * M - 1 := by simp only [hρ₆, cval_W, hcd]; omega
  -- their decoded values
  have hpowZ : ((2 : ℤ)) ^ (k + 2) = 4 * (A : ℤ) := by
    rw [hAdef, pow_succ, pow_succ]
    push_cast
    ring
  have hb₁ : bval ρ₁ = 4 * N - 1 := by
    rw [hρ₁, bval_Zrun, hpowZ, hN]
    ring
  have hb₂ : bval ρ₂ = 8 * N - 2 := by
    rw [hρ₂, bval_W, if_pos (show cval ρ₁ % 2 = 1 by omega), hb₁]
    ring
  have hb₃ : bval ρ₃ = 16 * N - 3 := by rw [hρ₃, bval_Z, hb₂]; ring
  have hb₄ : bval ρ₄ = 32 * N - 5 := by rw [hρ₄, bval_Z, hb₃]; ring
  have hb₅ : bval ρ₅ = 64 * N - 10 := by
    rw [hρ₅, bval_W, if_pos (show cval ρ₄ % 2 = 1 by omega), hb₄]
    ring
  have hbd : bval (cdec ρ₅) = 64 * N - 10 := by rw [bval_cdec hst₅ h5pos, hb₅]
  have hb₆ : bval ρ₆ = 32 * N - 6 := by
    rw [hρ₆, bval_W, if_neg (show ¬ cval (cdec ρ₅) % 2 = 1 by omega), hbd]
    omega
  -- the counts
  obtain ⟨hn₁, hn₂⟩ := nbit_Zrun (k + 2) σ
  have hadmh := hadm.head
  have hadm₁ : Adm ρ₁ := Adm_Zrun _ hadm
  have hadm₂ : Adm ρ₂ := adm_consW hadm₁ (by rw [hn₁, hn₂]; omega)
  have hadm₃ : Adm ρ₃ := adm_consZ hadm₂
  have hadm₄ : Adm ρ₄ := adm_consZ hadm₃
  have hadm₅ : Adm ρ₅ := adm_consW hadm₄ (by
    simp only [hρ₄, hρ₃, hρ₂, nbit_Z, nsh_Z, nbit_W, nsh_W]
    rw [hn₁, hn₂]
    omega)
  have hadmd : Adm (cdec ρ₅) := Adm.cdec hst₅ hadm₅ h5pos
  have hadm₆ : Adm ρ₆ := adm_consW hadmd (by
    rw [nbit_cdec, nsh_cdec]
    simp only [hρ₅, hρ₄, hρ₃, hρ₂, nbit_Z, nsh_Z, nbit_W, nsh_W]
    rw [hn₁, hn₂]
    omega)
  have hcount₆ : nsh ρ₆ + (k + 1) ≤ nbit ρ₆ := by
    simp only [hρ₆, hρ₅, hρ₄, hρ₃, hρ₂, nbit_Z, nsh_Z, nbit_W, nsh_W, nbit_cdec, nsh_cdec]
    rw [hn₁, hn₂]
    omega
  -- the tower of pops at the end of the word
  have hc₆' : cval ρ₆ = 2 ^ (k + 1) * (cval σ + 1) - 1 := by
    rw [hc₆, hM, hAdef, pow_succ]
    ring_nf
  obtain ⟨hst₇, hadm₇, hc₇, hb₇⟩ :=
    Wrun_facts (k + 1) ρ₆ (cval σ) hst₆ hadm₆ hc₆' hcount₆
  -- the run
  refine Returns.of_run (brun_Yrun (b4 := b4) (k + 2) σ _) ?_
  refine Returns.of_run (c' := ⟨ρ₂, .Rt, .Y :: .Y :: .V :: .X ::
    (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨ρ₃, .Rt, .Y :: .V :: .X ::
    (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨ρ₄, .Rt, .V :: .X ::
    (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨ρ₅, .Rt, .X ::
    (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨ρ₅, .Lt, .V ::
    (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  obtain ⟨k₅, hr₅⟩ := brun_cdec_of (b4 := b4) hst₅ h5pos (.V :: (List.replicate (k + 1) .V ++ [.R]))
  refine Returns.of_run hr₅ ?_
  refine Returns.of_run (c' := ⟨ρ₆, .Rt, List.replicate (k + 1) .V ++ [.R]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (brun_Vrun (b4 := b4) (k + 1) ρ₆ [.R]) ?_
  -- the drain at the right end
  refine returns_strong ⟨hst₇, hadm₇, ?_⟩
  rw [hc₇, hb₇, hb₆]
  have hApos : (1 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hA
  have hv0 : (0 : ℤ) ≤ (cval σ : ℤ) := Int.natCast_nonneg _
  have hvN : (cval σ : ℤ) + 1 ≤ N := by
    have hMv : (cval σ : ℤ) + 1 ≤ (M : ℤ) := by
      rw [hM]
      push_cast
      exact le_mul_of_one_le_left (by omega) hApos
    omega
  have hpowA : ((2 : ℤ)) ^ (k + 1) = 2 * (A : ℤ) := by
    rw [hAdef, pow_succ]
    push_cast
    ring
  rw [hpowA]
  have hkey : 2 * (A : ℤ) * (32 * N - 6) = (A : ℤ) * (64 * N - 12) := by ring
  rw [hkey]
  have hb : (64 * N - 12 : ℤ) ≤ (A : ℤ) * (64 * N - 12) :=
    le_mul_of_one_le_left (by omega) hApos
  omega

/-! ## The marker visit -/

/-- **The ordinary case**: the counter below the `141` block is at least two,
so the head pays the two decrements and pops, and the deposited word is reset
over the resulting stack. -/
theorem returns_j1_ord {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c) {T : List RB}
    (hcont : Returns b4 ⟨.W :: cdec (cdec c), .Rt, .P2 :: T⟩) :
    Returns b4 ⟨c, .Lt, .X :: .P2 :: T⟩ := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.X :: .P2 :: T)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P2 :: T)
  refine Returns.of_run (hr1.trans (BRun.head
    (show bstep b4 ⟨cdec c, .Rt, .X :: .P2 :: T⟩ = some (⟨cdec c, .Lt, .V :: .P2 :: T⟩, 1)
      from rfl)
    (hr2.trans (BRun.of_step
      (show bstep b4 ⟨cdec (cdec c), .Rt, .V :: .P2 :: T⟩
        = some (⟨.W :: cdec (cdec c), .Rt, .P2 :: T⟩, 2) from rfl))))) hcont

/-- **The exceptional case**: the counter below the `141` block is zero or one,
the head runs off the left end and the decoded word of the stack is reset
first; the two pending digits then cancel and the deposited word is read in the
counter phase, over a stack whose counter is odd and whose decoded value is at
least seven. -/
theorem returns_j1_small {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hv : cval c ≤ 1) (hmar : (cval c : ℤ) + 2 ≤ bval c)
    (heven : cval c % 2 = 0 → (cval c : ℤ) + 4 ≤ bval c)
    (hh : 2 ≤ nbit c - nsh c) {T : List RB}
    (hcont : ∀ σ : List LB, CStack σ → Adm σ → Good σ → cval σ % 2 = 1 → 7 ≤ bval σ →
      Returns b4 ⟨σ, .Rt, T⟩) :
    Returns b4 ⟨c, .Lt, .X :: .P2 :: T⟩ := by
  obtain ⟨hstt, hadmt, hgt, hcvt, -, hdich⟩ := paid_stack_facts hadm hg hh
  have hru : rrun (pdec c) 0 = bval c := (bval_eq_rrun c).symm
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hgth := hgt.head
  rcases (show cval c = 0 ∨ cval c = 1 by omega) with h0 | h1
  · -- the counter is already exhausted: the pop of the reset word is charged
    have hB : (4 : ℤ) ≤ bval c := by
      have := heven (by omega)
      omega
    have hw : Digs (pdec c ++ [RB.X]) := (pdec_digs c).append (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Or.inr (Or.inr rfl))
    have hcl : (0 : ℤ) ≤ rrun (pdec c ++ [RB.X]) (cval ([LB.L] : List LB)) := by
      rw [hL]
      simp only [Nat.cast_zero, rrun_append, rrun_cons, rrun_nil, rstep_X, hru]
      omega
    obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hst h0 (.X :: .P2 :: T)
    rw [ofw_eq_pdec hst h0,
      show pdec c ++ (RB.X :: .P2 :: T) = (pdec c ++ [RB.X]) ++ (.P2 :: T) by simp] at hr0
    refine Returns.of_run (hr0.trans (BRun.of_step
      (show bstep b4 ⟨[LB.L], .Lt, (pdec c ++ [RB.X]) ++ (.P2 :: T)⟩
        = some (⟨[LB.L], .Rt, .P2 :: ((pdec c ++ [RB.X]) ++ (.P2 :: T))⟩, 4) from rfl))) ?_
    refine returns_merge CStack.base hw hcl ?_
    obtain ⟨hsts, hadms, hgs, -, -, -⟩ :=
      tfold_props (pdec c ++ [RB.X]) hw CStack.base adm_L good_L hcl
    have hseq : tfold [LB.L] (pdec c ++ [RB.X]) = cdec (.W :: tfold [LB.L] (pdec c)) := by
      rw [tfold_append]
      rfl
    have hcvtB : (cval (tfold [LB.L] (pdec c)) : ℤ) = bval c := hcvt
    have hposW : 1 ≤ cval (.W :: tfold [LB.L] (pdec c)) := by
      simp only [cval_W]
      omega
    have hbs : bval (tfold [LB.L] (pdec c ++ [RB.X]))
        = bval (.W :: tfold [LB.L] (pdec c)) := by
      rw [hseq, bval_cdec hstt.consW hposW]
    have h3 : (3 : ℤ) ≤ bval (tfold [LB.L] (pdec c ++ [RB.X])) := by
      rw [hbs, bval_W]
      by_cases hpar : cval (tfold [LB.L] (pdec c)) % 2 = 1
      · rw [if_pos hpar]
        omega
      · rw [if_neg hpar]
        have h11 : (11 : ℤ) ≤ bval (tfold [LB.L] (pdec c)) := by
          rcases hdich with ho | hb
          · omega
          · exact hb
        omega
    refine hcont _ hsts.consZ (adm_consZ hadms) (good_consZ hgs) (by simp only [cval_Z]; omega) ?_
    simp only [bval_Z]
    omega
  · -- one decrement is available, and then the counter is exhausted
    have hB : (3 : ℤ) ≤ bval c := by omega
    have hpos1 : 1 ≤ cval c := by omega
    have hstd : CStack (cdec c) := cdec_CStack_all hst
    have hcvd : cval (cdec c) = 0 := by rw [cdec_cval hst hpos1]; omega
    have hpdd : pdec (cdec c) = pdec c := pdec_cdec hst hpos1
    have hw : Digs (pdec c ++ [RB.V]) := (pdec_digs c).append (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Or.inr (Or.inl rfl))
    have hcl : (0 : ℤ) ≤ rrun (pdec c ++ [RB.V]) (cval ([LB.L] : List LB)) := by
      rw [hL]
      simp only [Nat.cast_zero, rrun_append, rrun_cons, rrun_nil, rstep_V, hru]
      omega
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst hpos1 (.X :: .P2 :: T)
    obtain ⟨k0, hr0⟩ := brun_overflow_of (b4 := b4) hstd hcvd (.V :: .P2 :: T)
    rw [ofw_eq_pdec hstd hcvd, hpdd,
      show pdec c ++ (RB.V :: .P2 :: T) = (pdec c ++ [RB.V]) ++ (.P2 :: T) by simp] at hr0
    refine Returns.of_run (hr1.trans (BRun.head
      (show bstep b4 ⟨cdec c, .Rt, .X :: .P2 :: T⟩
        = some (⟨cdec c, .Lt, .V :: .P2 :: T⟩, 1) from rfl)
      (hr0.trans (BRun.of_step
        (show bstep b4 ⟨[LB.L], .Lt, (pdec c ++ [RB.V]) ++ (.P2 :: T)⟩
          = some (⟨[LB.L], .Rt, .P2 :: ((pdec c ++ [RB.V]) ++ (.P2 :: T))⟩, 4)
          from rfl))))) ?_
    refine returns_merge CStack.base hw hcl ?_
    obtain ⟨hsts, hadms, hgs, -, -, -⟩ :=
      tfold_props (pdec c ++ [RB.V]) hw CStack.base adm_L good_L hcl
    have hseq : tfold [LB.L] (pdec c ++ [RB.V]) = .X :: tfold [LB.L] (pdec c) := by
      rw [tfold_append]
      rfl
    have hcvtB : (cval (tfold [LB.L] (pdec c)) : ℤ) = bval c := hcvt
    have h3 : (3 : ℤ) ≤ bval (tfold [LB.L] (pdec c ++ [RB.V])) := by
      rw [hseq, bval_X]
      omega
    refine hcont _ hsts.consZ (adm_consZ hadms) (good_consZ hgs) (by simp only [cval_Z]; omega) ?_
    simp only [bval_Z]
    omega

/-! ## The stack the two decrements and the pop leave behind -/

/-- The two decrements and the pop of the ordinary case leave a good stack, and
its counter and decoded value are the ones of `values_W_cdec2`. -/
theorem tau_facts {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (h2 : 2 ≤ cval c) :
    CStack (.W :: cdec (cdec c)) ∧ Adm (.W :: cdec (cdec c)) ∧ Good (.W :: cdec (cdec c)) ∧
      cval (.W :: cdec (cdec c)) = (cval c - 2) / 2 ∧
      bval (.W :: cdec (cdec c)) =
        if (cval c - 2) % 2 = 1 then 2 * bval c else bval c / 2 - 1 := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hadmd : Adm (cdec c) := Adm.cdec hst hadm h1
  have hgd : Good (cdec c) := Good.cdec hst hg h1
  have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have hbv : bval (cdec c) = bval c := bval_cdec hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  have hstd2 : CStack (cdec (cdec c)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec c)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec c)) := Good.cdec hstd hgd h1'
  have hcv2 : cval (cdec (cdec c)) = cval c - 2 := by rw [cdec_cval hstd h1', hcv]; omega
  have hbv2 : bval (cdec (cdec c)) = bval c := by rw [bval_cdec hstd h1', hbv]
  have hun : 2 ≤ nbit c - nsh c := two_le_unmatched hst hadm h2
  have hgh := hg.head
  have hcast : ((cval c - 2 : ℕ) : ℤ) = (cval c : ℤ) - 2 := by omega
  obtain ⟨hcvW, hbvW⟩ := values_W_cdec2 hst h2
  refine ⟨hstd2.consW, adm_consW hadmd2 ?_, good_consW hgd2 ?_, hcvW, hbvW⟩
  · rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
    omega
  · rw [hcv2, hbv2, hcast]
    omega

/-- The ordinary case, when the word the marker deposited is followed by a
pending `2>` and the tail: the word is reset over the stack and the two pending
digits then cancel. -/
theorem returns_tau_Yrun {τ : List LB} (hst : CStack τ) (hadm : Adm τ) (hg : Good τ)
    {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w (cval τ)) :
    Returns b4 ⟨τ, .Rt, .P2 :: (w ++ (.P2 :: (List.replicate 2 .Y ++ [.R1])))⟩ := by
  refine returns_merge hst hw hcl ?_
  obtain ⟨h1, h2, h3, -, -, -⟩ := tfold_props w hw hst hadm hg hcl
  exact returns_Yrun h1.consZ (adm_consZ h2) (good_consZ h3) (by omega) (Or.inl (by omega))

/-! ## The local episode, for every number of one bits above the marker -/

/-- The episode with no one bit above the marker: the word the marker deposits
is the residual `11 2> 22 22 1$` itself. -/
theorem core1RB_zero {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hmar : (cval c : ℤ) + 2 ≤ bval c)
    (heven : cval c % 2 = 0 → (cval c : ℤ) + 4 ≤ bval c)
    (hh : 2 ≤ nbit c - nsh c) :
    Returns b4 ⟨.J1 :: c, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  refine Returns.of_run (BRun.of_step (j1_step (b4 := b4) c _)) ?_
  rcases (show cval c ≤ 1 ∨ 2 ≤ cval c by omega) with hsm | h2
  · exact returns_j1_small hst hadm hg hsm hmar heven hh
      (fun _ h1 h2 h3 h4 h5 => returns_ct0 h1 h2 h3 h4 h5)
  · obtain ⟨hstτ, hadmτ, hgτ, hcvτ, hbvτ⟩ := tau_facts hst hadm hg h2
    refine returns_j1_ord hst h2 ?_
    set τ : List LB := .W :: cdec (cdec c) with hτ
    rcases (show cval τ ≤ 1 ∨ 2 ≤ cval τ by omega) with hτ1 | hτ2
    · -- the pop of the reset is unpaid: the head turns around once more and the
      -- pending `1>` runs into the tail
      have hstW : CStack (.W :: τ) := hstτ.consW
      have hadmW : Adm (.W :: τ) := adm_consW hadmτ (by
        rw [hτ]
        simp only [nbit_W, nsh_W, nbit_cdec, nsh_cdec]
        omega)
      have hgW : Good (.W :: τ) := by
        by_cases hodd : cval τ % 2 = 1
        · exact good_consW_odd hgτ hodd
        · have h0 : cval τ = 0 := by omega
          have hc23 : cval c = 2 ∨ cval c = 3 := by omega
          refine good_consW hgτ ?_
          rw [h0]
          rcases hc23 with hc | hc
          · have h6 := heven (by omega)
            rw [hbvτ, hc]
            norm_num
            omega
          · rw [hbvτ, hc]
            norm_num
            omega
      refine Returns.of_run (BRun.head
        (show bstep b4 ⟨τ, .Rt, .P2 :: .X :: .P2 :: [RB.Y, .Y, .R1]⟩
          = some (⟨τ, .Rt, .V :: .P1 :: .P2 :: [RB.Y, .Y, .R1]⟩, 0) from rfl)
        (BRun.head (show bstep b4 ⟨τ, .Rt, .V :: .P1 :: .P2 :: [RB.Y, .Y, .R1]⟩
            = some (⟨.W :: τ, .Rt, .P1 :: .P2 :: [RB.Y, .Y, .R1]⟩, 2) from rfl)
          (BRun.head (show bstep b4 ⟨.W :: τ, .Rt, .P1 :: .P2 :: [RB.Y, .Y, .R1]⟩
              = some (⟨.W :: τ, .Rt, .U :: [RB.Y, .Y, .R1]⟩, 0) from rfl)
            (BRun.of_step (show bstep b4 ⟨.W :: τ, .Rt, .U :: [RB.Y, .Y, .R1]⟩
              = some (⟨.W :: τ, .Lt, .Y :: [RB.Y, .Y, .R1]⟩, 1) from rfl))))) ?_
      refine returns_Y3 hstW hadmW hgW ?_
      have hhd := hgW.head
      have h0 : (0 : ℤ) ≤ cval (.W :: τ) := Int.natCast_nonneg _
      omega
    · have hcl : (0 : ℤ) ≤ rrun [RB.X] (cval τ) := by
        simp only [rrun_cons, rrun_nil, rstep_X]
        omega
      have hres := returns_tau_Yrun (b4 := b4) hstτ hadmτ hgτ (w := [RB.X])
        (Digs.cons (Or.inr (Or.inr rfl)) Digs.nil) hcl
      simpa using hres

/-- The episode with one one bit above the marker. -/
theorem core1RB_one {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hmar : (cval c : ℤ) + 2 ≤ bval c)
    (heven : cval c % 2 = 0 → (cval c : ℤ) + 4 ≤ bval c)
    (hh : 2 ≤ nbit c - nsh c) :
    Returns b4 ⟨.Z :: .J1 :: c, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  refine Returns.of_run (c' := ⟨.X :: .J1 :: c, .Rt, [.X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.X :: .J1 :: c, .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.J1 :: c, .Lt, [.Y, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (BRun.of_step (j1_step (b4 := b4) c _)) ?_
  rcases (show cval c ≤ 1 ∨ 2 ≤ cval c by omega) with hsm | h2
  · exact returns_j1_small hst hadm hg hsm hmar heven hh
      (fun _ h1 h2 h3 _ _ => returns_ct1 h1 h2 h3)
  · obtain ⟨hstτ, hadmτ, hgτ, hcvτ, hbvτ⟩ := tau_facts hst hadm hg h2
    refine returns_j1_ord hst h2 ?_
    set τ : List LB := .W :: cdec (cdec c) with hτ
    have hcl : (0 : ℤ) ≤ rrun [RB.Y, RB.V] (cval τ) := by
      simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V]
      have h0 : (0 : ℤ) ≤ cval τ := Int.natCast_nonneg _
      omega
    have hres := returns_tau_Yrun (b4 := b4) hstτ hadmτ hgτ (w := [RB.Y, RB.V])
      (Digs.cons (Or.inl rfl) (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)) hcl
    simpa using hres

/-- The episode with at least two one bits above the marker: the local counter
drains onto the marker and deposits `kword`. -/
theorem core1RB_big {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hmar : (cval c : ℤ) + 2 ≤ bval c)
    (heven : cval c % 2 = 0 → (cval c : ℤ) + 4 ≤ bval c)
    (hh : 2 ≤ nbit c - nsh c) (k : ℕ) :
    Returns b4 ⟨List.replicate (k + 2) .Z ++ .J1 :: c, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  refine marker_drain k ?_
  refine Returns.of_run (BRun.of_step (j1_step (b4 := b4) c _)) ?_
  rcases (show cval c ≤ 1 ∨ 2 ≤ cval c by omega) with hsm | h2
  · exact returns_j1_small hst hadm hg hsm hmar heven hh
      (fun _ h1 h2 h3 _ _ => returns_ctk h1 h2 h3 k)
  · obtain ⟨hstτ, hadmτ, hgτ, hcvτ, hbvτ⟩ := tau_facts hst hadm hg h2
    refine returns_j1_ord hst h2 ?_
    set τ : List LB := .W :: cdec (cdec c) with hτ
    have hend : kword (k + 2)
        = (List.replicate (k + 2) RB.Y ++ [.V, .Y, .Y, .V, .X] ++ List.replicate k .V)
          ++ [.V] := by
      rw [kword]
      simp [List.replicate_succ']
    have hpos : 1 ≤ rrun (kword (k + 2)) (cval τ) := by
      have h0 := rrun_kword_pos (k + 2) (by omega)
      have hmono : rrun (kword (k + 2)) 0 ≤ rrun (kword (k + 2)) (cval τ) :=
        rrun_mono _ (Int.natCast_nonneg _)
      omega
    exact returns_reset_end hstτ hadmτ hgτ (digs_kword _) hend hpos

/-- **The local episode of `1RB`.** -/
theorem core1RB {c : List LB} (hst : CStack c) (hadm : Adm c) (hg : Good c)
    (hmar : (cval c : ℤ) + 2 ≤ bval c)
    (heven : cval c % 2 = 0 → (cval c : ℤ) + 4 ≤ bval c)
    (hh : 2 ≤ nbit c - nsh c) (n : ℕ) :
    Returns b4 ⟨List.replicate n .Z ++ .J1 :: c, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  match n with
  | 0 => simpa using core1RB_zero hst hadm hg hmar heven hh
  | 1 => simpa using core1RB_one hst hadm hg hmar heven hh
  | (k + 2) => exact core1RB_big hst hadm hg hmar heven hh k

/-- **The `W` case of the sweep for `1RB`.** -/
theorem wcase_1RB : WCase b4_1RB :=
  wcase_of_core gStep_1RB (fun _ n h1 h2 h3 h4 h5 h6 => core1RB h1 h2 h3 h4 h5 h6 n)

end BB25.Prefix
