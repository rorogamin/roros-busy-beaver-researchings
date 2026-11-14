/-
# The member `2RA`

Its `A> 241` rule is

```
  A> 241  ⟶  001 A>        (five base steps)
```

so the `241` block becomes the block `K0 = 001` on the left stack.  Unlike the
markers of `0RA` and `2RB`, `K0` is **not** a movable left end: when the head
first comes back to it,

```
  K0 <A  ⟶  01 A>
```

which is exactly what a one bit `Z = 01` does — the bit is cleared and the head
turns around — except that the cleared bit is the marker `K1 = 011`.  Only at
the *second* leftward visit,

```
  K1 <A  ⟶  11 A> 2>,
```

does the marker behave like a left end and create a pending `2>`.

So the `K0` of `2RA` is the leading one bit of the local counter the sweep
builds, and the local episode has two halves: the counter *above* `K0` drains
and overflows onto it (this is the drain of `0RA`, with `K0 c` as its foreign
bottom), the marker becomes `K1` and the head turns around **without** a
pending digit, so it re-reads the deposited word in the *counter phase*; that
rebuilds an exhausted counter, which overflows onto `K1`, and now the marker
rule does create the pending `2>` and the ordinary reset finishes the episode.

The counter phase has no general theory here — and cannot have one, since the
rebuilt stack is not good in general.  It does not need one: by
`drain_rep_word` the deposited word is known exactly,

```
  P(σ') = 22^n 21 22 22 21 11 21^(n-2),
```

and the counter phase re-reads that *explicit* word.  The stack it rebuilds is
exhausted and deposits the same word again, one `21` block longer.
-/
import RequestProject.BB25.Prefix.DrainWord
import RequestProject.BB25.Prefix.Marker

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The two rules of the marker -/

/-- The first leftward visit: the marker behaves like a one bit. -/
theorem k0_step (c2 : List LB) (rt : List RB) :
    bstep b4 ⟨.K0 :: c2, .Lt, rt⟩ = some (⟨.K1 :: c2, .Rt, rt⟩, 3) := rfl

/-! ## The end of the episode -/

/-- **The second leftward visit.**  The head arrives at `K1` with a clean word
of positive value in front of the right end; the marker turns it around with a
pending `2>`, and the ordinary reset over the good stack `11 c` reaches a safe
checkpoint. -/
theorem marker_end {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2)
    {w : List RB} (hw : Digs w) (hpos : 1 ≤ rrun w 0) :
    Returns b4 ⟨.K1 :: c2, .Lt, w ++ [.V, .R]⟩ := by
  set π : List LB := .X :: c2 with hπ
  refine Returns.of_run (c' := ⟨π, .Rt, .P2 :: (w ++ [.V, .R])⟩)
    (BRun.of_step (markTurn_K1 (b4 := b4) c2 _)) ?_
  have happ : w ++ [RB.V, RB.R] = (w ++ [RB.V]) ++ [RB.R] := by simp
  rw [happ]
  refine returns_reset_end hst.consX (adm_consX hadm) (good_consX hg)
    (hw.append ?_) rfl ?_
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact Or.inr (Or.inl rfl)
  · have hmono : rrun w 0 ≤ rrun w (cval (LB.X :: c2)) := rrun_mono _ (Int.natCast_nonneg _)
    rw [rrun_append]
    simp only [rrun_cons, rrun_nil, rstep_V]
    omega

/-! ## The episode with no one bit above the marker -/

/-- `n = 0`: the head clears the marker at once, comes back to it and the
pending `2>` it then creates runs into the `22` tail. -/
theorem core2RA_zero {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2) :
    Returns b4 ⟨.K0 :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  refine Returns.of_run (c' := ⟨.K1 :: c2, .Rt, [.X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step (k0_step c2 _)) ?_
  refine Returns.of_run (c' := ⟨.K1 :: c2, .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.X :: c2, .Rt, [.P2, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step (markTurn_K1 (b4 := b4) c2 _)) ?_
  refine Returns.of_run (c' := ⟨.X :: c2, .Rt, [.Y, .P1, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .X :: c2, .Rt, [.P1, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .X :: c2, .Rt, [.U, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .X :: c2, .Lt, [.Y, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.X :: .X :: c2, .Rt, [.Y, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  have he : ([.Y, .Y, .Y, .R1] : List RB) = List.replicate 3 RB.Y ++ [RB.R1] := rfl
  rw [he]
  exact returns_Yrun hst.consX.consX (adm_consX (adm_consX hadm))
    (good_consX (good_consX hg)) (by omega) (Or.inl (by omega))

/-! ## The counter phase -/

/-- **The free re-reading of the deposited word.**  The head has just cleared
the marker and turned around *without* a pending digit, so it reads the word
`kword n` as a fresh counter: a `22` block pushes a one bit, a `21` block
pushes a pop and the single `11` block costs one decrement.  The counter it
builds is exhausted, and the word it will deposit is the same `kword n`. -/
theorem free_cycle {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2) (k : ℕ) :
    Returns b4 ⟨.K1 :: c2, .Rt, kword (k + 2) ++ [.R]⟩ := by
  set β : List LB := .K1 :: c2 with hβ
  set n : ℕ := k + 2 with hn
  have hpow : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowk : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hnk : 2 ^ n = 2 * 2 ^ (k + 1) := by rw [hn, pow_succ]; ring
  -- the stacks the counter phase builds
  set s₁ : List LB := List.replicate n .Z ++ [.L] with hs₁
  set s₂ : List LB := .W :: s₁ with hs₂
  set s₃ : List LB := .Z :: s₂ with hs₃
  set s₄ : List LB := .Z :: s₃ with hs₄
  set s₅ : List LB := .W :: s₄ with hs₅
  set s₆ : List LB := .W :: cdec s₅ with hs₆
  set ρ : List LB := List.replicate (k + 1) .W ++ s₆ with hρ
  -- their counters
  have hc₁ : cval s₁ = 2 ^ n - 1 := by rw [hs₁, cval_Zrun]; simp
  have hc₂ : cval s₂ = 2 ^ (k + 1) - 1 := by rw [hs₂, cval_W, hc₁]; omega
  have hc₃ : cval s₃ = 2 ^ n - 1 := by rw [hs₃, cval_Z, hc₂]; omega
  have hc₄ : cval s₄ = 2 * 2 ^ n - 1 := by rw [hs₄, cval_Z, hc₃]; omega
  have hc₅ : cval s₅ = 2 ^ n - 1 := by rw [hs₅, cval_W, hc₄]; omega
  -- their stack structure
  have hst₁ : CStack s₁ := CStack_Zrun _ CStack.base
  have hst₂ : CStack s₂ := hst₁.consW
  have hst₃ : CStack s₃ := hst₂.consZ
  have hst₄ : CStack s₄ := hst₃.consZ
  have hst₅ : CStack s₅ := hst₄.consW
  have hcd : cval (cdec s₅) = 2 ^ n - 2 := by
    rw [cdec_cval hst₅ (by omega), hc₅]
    omega
  have hstd : CStack (cdec s₅) := cdec_CStack_all hst₅
  have hst₆ : CStack s₆ := hstd.consW
  have hc₆ : cval s₆ = 2 ^ (k + 1) - 1 := by rw [hs₆, cval_W, hcd]; omega
  have hstρ : CStack ρ := CStack_Wrun _ hst₆
  have hcρ : cval ρ = 0 := by
    rw [hρ, cval_Wrun, hc₆]
    exact Nat.div_eq_of_lt (by omega)
  -- their decoded words
  have hp₁ : pdec s₁ = List.replicate n .Y := by rw [hs₁, pdec_Zrun]; simp
  have hp₂ : pdec s₂ = List.replicate n .Y ++ [.V] := by
    rw [hs₂, pdec_W, if_pos (by omega), hp₁]
  have hp₃ : pdec s₃ = List.replicate n .Y ++ [.V, .Y] := by
    rw [hs₃, pdec_Z, hp₂]; simp
  have hp₄ : pdec s₄ = List.replicate n .Y ++ [.V, .Y, .Y] := by
    rw [hs₄, pdec_Z, hp₃]; simp
  have hp₅ : pdec s₅ = List.replicate n .Y ++ [.V, .Y, .Y, .V] := by
    rw [hs₅, pdec_W, if_pos (by omega), hp₄]; simp
  have hp₆ : pdec s₆ = List.replicate n .Y ++ [.V, .Y, .Y, .V, .X] := by
    rw [hs₆, pdec_W, if_neg (by omega), pdec_cdec hst₅ (by omega), hp₅]; simp
  have hpρ : pdec ρ = kword n := by
    rw [hρ, pdec_Wrun_ones _ _ hc₆, hp₆, kword]
    simp [hn]
  -- the run
  have hword : kword n ++ [RB.R]
      = List.replicate n .Y ++ (.V :: .Y :: .Y :: .V :: .X ::
          (List.replicate (k + 1) .V ++ [.R])) := by
    rw [kword]
    simp [hn]
  rw [hword]
  have hr₁ : BRun b4 ⟨β, .Rt, List.replicate n .Y ++ (.V :: .Y :: .Y :: .V :: .X ::
        (List.replicate (k + 1) .V ++ [.R]))⟩
      ⟨rep β s₁, .Rt, .V :: .Y :: .Y :: .V :: .X :: (List.replicate (k + 1) .V ++ [.R])⟩
      (2 * n) := by
    have := brun_Yrun (b4 := b4) n β
      (.V :: .Y :: .Y :: .V :: .X :: (List.replicate (k + 1) .V ++ [.R]))
    rwa [show rep β s₁ = List.replicate n .Z ++ β by rw [hs₁, rep_Zrun, rep_L]]
  refine Returns.of_run hr₁ ?_
  refine Returns.of_run (c' := ⟨rep β s₂, .Rt, .Y :: .Y :: .V :: .X ::
      (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨rep β s₃, .Rt, .Y :: .V :: .X ::
      (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨rep β s₄, .Rt, .V :: .X ::
      (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨rep β s₅, .Rt, .X ::
      (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨rep β s₅, .Lt, .V ::
      (List.replicate (k + 1) .V ++ [.R])⟩) (BRun.of_step rfl) ?_
  obtain ⟨k₅, hr₅⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hst₅ (by omega)
    (.V :: (List.replicate (k + 1) .V ++ [.R]))
  refine Returns.of_run hr₅ ?_
  refine Returns.of_run (c' := ⟨rep β s₆, .Rt, List.replicate (k + 1) .V ++ [.R]⟩)
    (BRun.of_step rfl) ?_
  have hr₆ := brun_Vrun (b4 := b4) (k + 1) (rep β s₆) [.R]
  rw [show (List.replicate (k + 1) LB.W ++ rep β s₆) = rep β ρ by rw [hρ, rep_Wrun]] at hr₆
  refine Returns.of_run hr₆ ?_
  -- the right end and the overflow onto the marker
  refine Returns.of_run (c' := ⟨rep β ρ, .Lt, [.V, .R]⟩) (BRun.of_step rfl) ?_
  obtain ⟨k₇, hr₇⟩ := brun_overflow_rep_of (b4 := b4) (β := β) hstρ hcρ [.V, .R]
  rw [ofw_eq_pdec hstρ hcρ, hpρ] at hr₇
  refine Returns.of_run hr₇ ?_
  exact marker_end hst hadm hg (digs_kword n) (rrun_kword_pos n (by omega))

/-! ## The episode with one one bit above the marker -/

/-- `n = 1`: the single one bit is cleared at once and the overflow clears the
marker; the pending `2>` tail then builds the small counter `03 01 01 03 01`,
which drains in one round and overflows onto the marker. -/
theorem core2RA_one {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2) :
    Returns b4 ⟨.Z :: .K0 :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  set β : List LB := .K1 :: c2 with hβ
  set σ : List LB := [.W, .Z, .Z, .W, .Z, .L] with hσ
  have hstσ : CStack σ := CStack.base.consZ.consW.consZ.consZ.consW
  have hcvσ : cval σ = 1 := by rw [hσ]; rfl
  have hbvσ : bval σ = 22 := by rw [hσ]; rfl
  have hpdσ : pdec σ = [.Y, .V, .Y, .Y, .V] := by rw [hσ]; rfl
  have hadmσ : Adm σ :=
    adm_consW (adm_consZ (adm_consZ (adm_consW (adm_consZ adm_L) (by decide)))) (by decide)
  have hgσ : Good σ :=
    good_consW_odd (good_consZ (good_consZ (good_consW_odd (good_consZ good_L) (by rfl))))
      (by rfl)
  -- the bit, the marker and the pending tail
  refine Returns.of_run (c' := ⟨.X :: .K0 :: c2, .Rt, [.X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.X :: .K0 :: c2, .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.K0 :: c2, .Lt, [.Y, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨β, .Rt, [.Y, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step (k0_step c2 _)) ?_
  refine Returns.of_run (c' := ⟨.Z :: β, .Rt, [.V, .P2, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: .Z :: β, .Rt, [.P2, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: .Z :: β, .Rt, [.Y, .P2, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .W :: .Z :: β, .Rt, [.P2, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .W :: .Z :: β, .Rt, [.Y, .P2, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .Z :: .W :: .Z :: β, .Rt, [.P2, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .Z :: .W :: .Z :: β, .Rt, [.V, .R]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: .Z :: .Z :: .W :: .Z :: β, .Rt, [.R]⟩)
    (BRun.of_step rfl) ?_
  -- the drain of the small counter
  have hrw : (.W :: .Z :: .Z :: .W :: .Z :: β : List LB) = rep β σ := rfl
  rw [hrw]
  obtain ⟨σ', k₃, hS', hcv', hb', hword', hr₃⟩ :=
    drain_rep_word_of (b4 := b4) (β := β) (σ := σ)
      ⟨hstσ, hadmσ, hgσ, by rw [hcvσ, hbvσ]; norm_num⟩
  refine Returns.of_run hr₃ ?_
  have hd1 : dword 1 = [RB.X] := by rw [dword_succ]; norm_num [dword_zero]
  have hw : pdec σ' = kword 1 := by
    rw [hword', hcvσ, hpdσ, hd1, kword]
    rfl
  rw [hw]
  exact marker_end hst hadm hg (digs_kword 1) (rrun_kword_pos 1 (by omega))

/-! ## The episode with two or more one bits above the marker -/

/-- `n ≥ 2`: the counter above the marker really drains.  Its overflow clears
the marker, and `free_cycle` finishes the episode. -/
theorem core2RA_big {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2) (k : ℕ) :
    Returns b4 ⟨List.replicate (k + 2) .Z ++ .K0 :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  refine marker_drain k ?_
  -- the marker is cleared and the head re-reads the deposited word
  refine Returns.of_run (c' := ⟨.K1 :: c2, .Rt, kword (k + 2) ++ [.R]⟩)
    (BRun.of_step (k0_step c2 _)) ?_
  exact free_cycle hst hadm hg k

/-! ## The `W` case of the sweep for `2RA` -/

/-- **The local episode of `2RA`**, for every number of one bits the sweep
leaves above the marker. -/
theorem core2RA {c2 : List LB} (hst : CStack c2) (hadm : Adm c2) (hg : Good c2) (n : ℕ) :
    Returns b4 ⟨List.replicate n .Z ++ .K0 :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  match n with
  | 0 => simpa using core2RA_zero hst hadm hg
  | 1 => simpa using core2RA_one hst hadm hg
  | (k + 2) => exact core2RA_big hst hadm hg k

/-- The `A> 241` rule of `2RA`. -/
theorem gStep_2RA (lt : List LB) (rest : List RB) :
    gStep b4_2RA lt rest = some (⟨.K0 :: lt, .Rt, rest⟩, 5) := rfl

/-- **The `W` case of the sweep for `2RA`.** -/
theorem wcase_2RA : WCase b4_2RA :=
  wcase_of_core gStep_2RA (fun _ n h1 h2 h3 _ _ _ => core2RA h1 h2 h3 n)

end BB25.Prefix
