/-
# The members whose `A> 241` rule pushes a one-use marker block

For

```
  0RA :  A> 241  ⟶  011 A>        (five base steps)
  2RB :  A> 241  ⟶  023 A>        (three base steps)
```

the `241` block becomes a *marker block* on the left stack (`K1 = 011`,
`J = 023`) and the head carries on to the right.  Both markers obey the same
rule when the head eventually comes back to them,

```
  K1 <A  ⟶  11 A> 2>      J <A  ⟶  11 A> 2>
```

(`MarkTurn`): the marker turns into a zero bit, the head turns around and a
pending `2>` is created — exactly what the left end of the tape does, except
that the bit is left behind.  So the marker is a *movable left end*: the
counter the sweep then builds on top of it drains against it and overflows
into it, and only after that does the machine see the stack below again.

`marker_core` runs that whole local episode.  Its three cases are the length
`n` of the run of one bits the sweep leaves above the marker: `n = 0` and
`n = 1` are finite calculations, and for `n ≥ 2` the local counter really
drains (`drain_rep` of `Bottom.lean`) before it overflows.

Because the checkpoint the return theorem hands out ends in a zero bit, the
sweep always strips at least one `11` block, so `r ≥ 2` and `n = r - 2 ≥ 0`
is well defined.  This is where the strengthening of `SafeCP` is used.
-/
import RequestProject.BB25.Prefix.Bottom
import RequestProject.BB25.Prefix.Return

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The marker rule -/

/-- The rule of a one-use marker block: the head turns around, the marker
becomes a zero bit and a pending `2>` is created. -/
def MarkTurn (b4 : Option (Sym × Dir × St)) (m : LB) (k : ℕ) : Prop :=
  ∀ (c2 : List LB) (rt : List RB),
    bstep b4 ⟨m :: c2, .Lt, rt⟩ = some (⟨.X :: c2, .Rt, .P2 :: rt⟩, k)

theorem markTurn_K1 : MarkTurn b4 .K1 4 := fun _ _ => rfl
theorem markTurn_J : MarkTurn b4 .J 6 := fun _ _ => rfl

/-! ## The tail shared by all three cases -/

/-- After the marker has been consumed the head is at `<A` in front of the
tail `22 22 22 1$`, on a stack that is good and admissible: one decrement (or,
if the counter is exhausted, one overflow and reset) reaches a checkpoint. -/
theorem returns_Y3 {σ : List LB} (hst : CStack σ) (hadm : Adm σ) (hg : Good σ)
    (hb : (0 : ℤ) ≤ bval σ) :
    Returns b4 ⟨σ, .Lt, [.Y, .Y, .Y, .R1]⟩ := by
  have he : ([.Y, .Y, .Y, .R1] : List RB) = List.replicate 3 RB.Y ++ [RB.R1] := rfl
  rw [he]
  rcases Nat.eq_zero_or_pos (cval σ) with h0 | h1
  · -- the counter is exhausted: the head overflows and the word is reset
    obtain ⟨k, hrun⟩ :=
      brun_overflow_of (b4 := b4) hst h0 (List.replicate 3 RB.Y ++ [RB.R1])
    rw [ofw_eq_pdec hst h0] at hrun
    refine Returns.of_run hrun ?_
    refine Returns.of_run (BRun.of_step (show bstep b4
      ⟨[LB.L], .Lt, pdec σ ++ (List.replicate 3 RB.Y ++ [RB.R1])⟩
      = some (⟨[LB.L], .Rt, .P2 :: (pdec σ ++ (List.replicate 3 RB.Y ++ [RB.R1]))⟩, 4) from rfl)) ?_
    refine returns_reset_Yrun (pdec_digs σ) ?_ (by omega)
    rw [← bval_eq_rrun]
    exact hb
  · obtain ⟨k, hrun⟩ :=
      brun_cdec_of (b4 := b4) hst h1 (List.replicate 3 RB.Y ++ [RB.R1])
    refine Returns.of_run hrun ?_
    exact returns_Yrun (cdec_CStack_all hst) (Adm.cdec hst hadm h1) (Good.cdec hst hg h1)
      (by omega) (Or.inl (by omega))

/-! ## The local episode above the marker -/

section Core

variable {m : LB} {km : ℕ} {c2 : List LB}

/-- The marker is met at once: the sweep left no one bit above it. -/
theorem marker_core_zero (hm : MarkTurn b4 m km) (hst : CStack c2) (hadm : Adm c2)
    (hg : Good c2) (hmar : (cval c2 : ℤ) + 1 ≤ bval c2) :
    Returns b4 ⟨m :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  set π : List LB := .X :: c2 with hπ
  have hstπ : CStack π := hst.consX
  have hadmπ : Adm π := adm_consX hadm
  have hgπ : Good π := good_consX hg
  refine Returns.of_run (c' := ⟨π, .Rt, [.P2, .X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step (hm c2 _)) ?_
  refine Returns.of_run (c' := ⟨π, .Rt, [.V, .P1, .P2, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: π, .Rt, [.P1, .P2, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: π, .Rt, [.U, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: π, .Lt, [.Y, .Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  have hadmW : Adm (.W :: π) := adm_consW hadmπ (by
    simp only [hπ, nbit_X, nsh_X]
    exact Nat.succ_le_succ hadm.head)
  have hgW : Good (.W :: π) := hgπ.cons (by
    have hcvπ : cval π = 2 * cval c2 := rfl
    have hbvπ : bval π = 2 * bval c2 + 1 := rfl
    simp only [cval_W, bval_W, hcvπ, hbvπ]
    have hpar : (2 * cval c2) % 2 = 0 := by omega
    rw [if_neg (by omega)]
    have h1 : (2 * cval c2) / 2 = cval c2 := by omega
    rw [h1]
    have h2 : (2 * bval c2 + 1) / 2 = bval c2 := by omega
    rw [h2]
    omega)
  refine returns_Y3 hstπ.consW hadmW hgW ?_
  have := hgW.head
  have h0 : (0 : ℤ) ≤ cval (LB.W :: π) := Int.natCast_nonneg _
  omega

/-- One one bit above the marker: a single decrement empties the local counter
and the overflow meets the marker. -/
theorem marker_core_one (hm : MarkTurn b4 m km) (hst : CStack c2) (hadm : Adm c2)
    (hg : Good c2) :
    Returns b4 ⟨.Z :: m :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  set π : List LB := .X :: c2 with hπ
  have hstπ : CStack π := hst.consX
  have hadmπ : Adm π := adm_consX hadm
  have hgπ : Good π := good_consX hg
  refine Returns.of_run (c' := ⟨.X :: m :: c2, .Rt, [.X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.X :: m :: c2, .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨m :: c2, .Lt, [.Y, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨π, .Rt, [.P2, .Y, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step (hm c2 _)) ?_
  refine Returns.of_run (c' := ⟨π, .Rt, [.Y, .P2, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: π, .Rt, [.P2, .V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: π, .Rt, [.Y, .P1, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .Z :: π, .Rt, [.P1, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .Z :: π, .Rt, [.U, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .Z :: π, .Lt, [.Y, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine returns_Y3 (hstπ.consZ.consZ) (adm_consZ (adm_consZ hadmπ))
    (good_consZ (good_consZ hgπ)) ?_
  have := hgπ.head
  have h0 : (0 : ℤ) ≤ cval π := Int.natCast_nonneg _
  simp only [bval_Z]
  omega

/-- Two or more one bits above the marker: the local counter drains. -/
theorem marker_core_big (hm : MarkTurn b4 m km) (hst : CStack c2) (hadm : Adm c2)
    (hg : Good c2) (k : ℕ) :
    Returns b4 ⟨List.replicate (k + 2) .Z ++ m :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  set β : List LB := m :: c2 with hβ
  set π : List LB := .X :: c2 with hπ
  have hstπ : CStack π := hst.consX
  have hadmπ : Adm π := adm_consX hadm
  have hgπ : Good π := good_consX hg
  set p : List LB := List.replicate (k + 2) .Z ++ [.L] with hp
  have hstp : CStack p := CStack_Zrun _ CStack.base
  have hadmp : Adm p := Adm_Zrun _ adm_L
  have hgp : Good p := Good_Zrun _ good_L
  have hcvp : cval p = 2 ^ (k + 2) * (0 + 1) - 1 := cval_Zrun _ _
  have hpow : 4 ≤ 2 ^ (k + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcv3 : 3 ≤ cval p := by omega
  have hrep : rep β p = List.replicate (k + 2) .Z ++ β := by rw [hp, rep_Zrun, rep_L]
  rw [← hrep]
  -- two decrements and a pop
  have h1 : 1 ≤ cval p := by omega
  obtain ⟨k₁, hr₁⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hstp h1 [.X, .P2, .Y, .Y, .R1]
  have hstd : CStack (cdec p) := cdec_CStack_all hstp
  have hcvd : cval (cdec p) = cval p - 1 := cdec_cval hstp h1
  have h1' : 1 ≤ cval (cdec p) := by omega
  obtain ⟨k₂, hr₂⟩ := brun_cdec_rep_of (b4 := b4) (β := β) hstd h1' [.V, .P2, .Y, .Y, .R1]
  refine Returns.of_run hr₁ ?_
  refine Returns.of_run (c' := ⟨rep β (cdec p), .Lt, [.V, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run hr₂ ?_
  refine Returns.of_run (c' := ⟨.W :: rep β (cdec (cdec p)), .Rt, [.P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.W :: rep β (cdec (cdec p)), .Rt, [.Y, .P2, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .W :: rep β (cdec (cdec p)), .Rt, [.P2, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run (c' := ⟨.Z :: .W :: rep β (cdec (cdec p)), .Rt, [.Y, .P2, .R1]⟩)
    (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨.Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.P2, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨.Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.V, .R]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨.W :: .Z :: .Z :: .W :: rep β (cdec (cdec p)), .Rt, [.R]⟩) (BRun.of_step rfl) ?_
  -- the drain, against the marker
  have hrw : (.W :: .Z :: .Z :: .W :: rep β (cdec (cdec p)) : List LB)
      = rep β (.W :: .Z :: .Z :: .W :: cdec (cdec p)) := rfl
  rw [hrw]
  obtain ⟨σ', k₃, hS', hcv', hb', hr₃⟩ :=
    drain_rep_of (b4 := b4) (β := β) (strongG_entry hstp hadmp hgp (by omega))
  refine Returns.of_run hr₃ ?_
  -- the marker, and the reset of the deposited word over the base `11 c`
  refine Returns.of_run (c' := ⟨π, .Rt, .P2 :: (pdec σ' ++ [.V, .R])⟩)
    (BRun.of_step (hm c2 _)) ?_
  have happ : pdec σ' ++ [RB.V, RB.R] = (pdec σ' ++ [RB.V]) ++ [RB.R] := by simp
  rw [happ]
  refine returns_reset_end hstπ hadmπ hgπ ((pdec_digs σ').append ?_) rfl ?_
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact Or.inr (Or.inl rfl)
  · have hmono : rrun (pdec σ') 0 ≤ rrun (pdec σ') (cval π) :=
      rrun_mono _ (Int.natCast_nonneg _)
    have hb0 : bval σ' = rrun (pdec σ') 0 := bval_eq_rrun σ'
    rw [rrun_append]
    simp only [rrun_cons, rrun_nil, rstep_V]
    omega

/-- **The marker episode.** -/
theorem marker_core (hm : MarkTurn b4 m km) (hst : CStack c2) (hadm : Adm c2)
    (hg : Good c2) (hmar : (cval c2 : ℤ) + 1 ≤ bval c2) (n : ℕ) :
    Returns b4 ⟨List.replicate n .Z ++ m :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩ := by
  match n with
  | 0 => simpa using marker_core_zero hm hst hadm hg hmar
  | 1 => simpa using marker_core_one hm hst hadm hg
  | (k + 2) => exact marker_core_big hm hst hadm hg k

end Core

/-! ## The `W` case of the sweep for a marker member -/

/-- **The `W` case of the `<B1` sweep for a member that pushes a marker**,
granting the local episode above the marker.  The sweep itself — two
decrements, the `A> 241` rule, the run of `22` blocks and the turn at the
right end — does not depend on the marker rule. -/
theorem wcase_of_core {m : LB} {kG : ℕ}
    (hG : ∀ (lt : List LB) (rest : List RB),
      gStep b4 lt rest = some (⟨m :: lt, .Rt, rest⟩, kG))
    (hcore : ∀ (c2 : List LB) (n : ℕ), CStack c2 → Adm c2 → Good c2 →
      (cval c2 : ℤ) + 2 ≤ bval c2 →
      (cval c2 % 2 = 0 → (cval c2 : ℤ) + 4 ≤ bval c2) →
      2 ≤ nbit c2 - nsh c2 →
      Returns b4 ⟨List.replicate n .Z ++ m :: c2, .Lt, [.X, .P2, .Y, .Y, .R1]⟩) :
    WCase b4 := by
  intro c r hst hadm hg hv _ heven hr
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  set tail : List RB := List.replicate (j + 2) RB.Y ++ [RB.R1] with htail
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
  -- two decrements bring the head to the `241` block
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.F :: tail)
  have hsF : bstep b4 ⟨cdec c, .Rt, .F :: tail⟩ = some (⟨cdec c, .Lt, .G :: tail⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.G :: tail)
  have hsG : bstep b4 ⟨cdec (cdec c), .Rt, .G :: tail⟩
      = some (⟨m :: cdec (cdec c), .Rt, tail⟩, kG) := hG _ _
  refine Returns.of_run (hr1.trans (BRun.head hsF (hr2.trans (BRun.of_step hsG)))) ?_
  -- the head swallows the run of `22` blocks and turns at the right end
  set c2 : List LB := cdec (cdec c) with hc2
  refine Returns.of_run (brun_Yrun (j + 2) (m :: c2) [.R1]) ?_
  have hsplit : List.replicate (j + 2) LB.Z ++ (m :: c2)
      = .Z :: (List.replicate (j + 1) .Z ++ (m :: c2)) := by
    rw [List.replicate_succ, List.cons_append]
  rw [hsplit]
  refine Returns.of_run
    (c' := ⟨.Z :: (List.replicate (j + 1) .Z ++ (m :: c2)), .Lt, [.R2]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨.X :: (List.replicate (j + 1) .Z ++ (m :: c2)), .Rt, [.R2]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨.X :: (List.replicate (j + 1) .Z ++ (m :: c2)), .Bt, [.Y, .R1]⟩) (BRun.of_step rfl) ?_
  refine Returns.of_run
    (c' := ⟨List.replicate (j + 1) .Z ++ (m :: c2), .Bt, [.Y, .Y, .R1]⟩) (BRun.of_step rfl) ?_
  have hsplit2 : List.replicate (j + 1) LB.Z ++ (m :: c2)
      = .Z :: (List.replicate j .Z ++ (m :: c2)) := by
    rw [List.replicate_succ, List.cons_append]
  rw [hsplit2]
  refine Returns.of_run
    (c' := ⟨List.replicate j .Z ++ (m :: c2), .Lt, [.X, .P2, .Y, .Y, .R1]⟩)
    (BRun.of_step rfl) ?_
  have hgh : (cval c : ℤ) ≤ bval c := hg.head
  have hc : (2 : ℤ) ≤ (cval c : ℤ) := by exact_mod_cast hv
  have hcast : ((cval c - 2 : ℕ) : ℤ) = (cval c : ℤ) - 2 := by omega
  refine hcore c2 j hstd2 hadmd2 hgd2 ?_ ?_ ?_
  · rw [hcv2, hbv2, hcast]
    omega
  · intro hpar
    rw [hcv2] at hpar
    have hpar' : cval c % 2 = 0 := by omega
    have := heven hpar'
    rw [hcv2, hbv2, hcast]
    omega
  · have hun : 2 ≤ nbit c - nsh c := two_le_unmatched hst hadm hv
    rw [hc2]
    rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]
    exact hun

/-- **The `W` case of the `<B1` sweep for a member that pushes a one-use
marker.** -/
theorem wcase_of_marker {m : LB} {km kG : ℕ} (hm : MarkTurn b4 m km)
    (hG : ∀ (lt : List LB) (rest : List RB),
      gStep b4 lt rest = some (⟨m :: lt, .Rt, rest⟩, kG)) : WCase b4 :=
  wcase_of_core hG (fun _ n h1 h2 h3 h4 _ _ => marker_core hm h1 h2 h3 (by omega) n)

/-! ## The two members -/

theorem gStep_0RA (lt : List LB) (rest : List RB) :
    gStep b4_0RA lt rest = some (⟨.K1 :: lt, .Rt, rest⟩, 5) := rfl

theorem gStep_2RB (lt : List LB) (rest : List RB) :
    gStep b4_2RB lt rest = some (⟨.J :: lt, .Rt, rest⟩, 3) := rfl

/-- **The `W` case of the sweep for `0RA`.** -/
theorem wcase_0RA : WCase b4_0RA := wcase_of_marker markTurn_K1 gStep_0RA

/-- **The `W` case of the sweep for `2RB`.** -/
theorem wcase_2RB : WCase b4_2RB := wcase_of_marker markTurn_J gStep_2RB

end BB25.Prefix
