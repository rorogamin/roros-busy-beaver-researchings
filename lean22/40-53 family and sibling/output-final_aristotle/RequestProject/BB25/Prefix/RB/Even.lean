/-
# The `01` branch of the `0RB` sweep after the first pop

`Sweep.lean` reduced non-halting of `0RB` to the two `01` branches of its
`<B1` sweep.  The first of them, `ZOdd`, is the member-independent branch and
is already closed in `Final.lean`.  This file is Section 8 of the submitted
argument: the branch met *after* the first pop, where the word in front of the
head is a generated word `w` over the bare right end.

Writing `a` for the counter of the stack `c` under the `01`, the branch splits
into four cases.

* `a ≥ 2` — the ordinary case.  The head spends two decrements, pops, and the
  pending `2>` resets `w` over the resulting stack; the right end then turns
  the head straight into a checkpoint.  That the checkpoint is good, positive
  and ready is Lemma A (`LemmaA.lean`).
* `a ≥ 2` with `w = w0 2` over an exhausted reset — the one exception of
  Lemma A.
* `a ≤ 1` — the counter is spent before the pop, so the stack overflows and
  deposits its decoded word in front of `w`.
* `a = 0` with a dirty early reset.
-/
import RequestProject.BB25.Prefix.RB.Early

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The ordinary case: a clean reset straight into a checkpoint -/

/-- **The ordinary case of the branch.**  A generated word over a good, strict
stack with a nonnegative counter returns to a checkpoint, unless it is the
unextended base word `w0 2` over an exhausted counter. -/
theorem sret0_gen_reset {π : List LB} (hst : CStack π) (hadm : Adm π) (hg : Good π)
    (hstr : Strict π) {w : List RB} {h : ℕ} (hgen : Gen w h)
    (hexc : w ≠ w0 2 ∨ 1 ≤ cval π) :
    SRet b4 ⟨π, .Rt, .P2 :: (w ++ [.R])⟩ := by
  obtain ⟨u, hu⟩ := gen_end_V hgen
  have ha : (0 : ℤ) ≤ (cval π : ℤ) := Int.natCast_nonneg _
  have hpos : 1 ≤ rrun w (cval π) := by
    refine gen_rrun_pos hgen ha ?_
    rcases hexc with hne | h1
    · exact Or.inl hne
    · exact Or.inr (by exact_mod_cast h1)
  exact sret0_reset_end hst hadm hg hstr hgen.digs hu hpos
    (ready_tfold_of_stops hgen.digs hst hadm hg (by omega) (gen_scan_stops hgen ha))

/-! ## The four cases of the branch -/

/-- **Case 8.2: the exceptional reset.**  The word `w0 2 = Y X Y Y V` over an
exhausted counter: the leading one bit is pushed, the following pop empties the
stack again and its pending decrement fails, so the machine overflows with the
word `P(q) Y` in front of it and reads the balanced `Y V` in the counter phase.
The reset word it finally rebuilds is the small clock of Section 7. -/
theorem sret0_exc {z : List LB} (hst : CStack z) (hg : Good z) (hv : cval z = 0) :
    SRet b4 ⟨z, .Rt, .P2 :: (w0 2 ++ [.R])⟩ := by
  have hB0 : 0 ≤ bval z := by
    have h := hg.head
    rw [hv] at h
    simpa using h
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  -- the leading one bit and the pop
  set q : List LB := .W :: .Z :: z with hq
  have hstq : CStack q := hst.consZ.consW
  have hcvZ : cval (.Z :: z) = 1 := by simp [cval_Z, hv]
  have hcvq : cval q = 0 := by rw [hq, cval_W, hcvZ]
  have hbvq : bval q = 4 * bval z + 2 := by
    rw [hq, bval_W, if_pos (by rw [hcvZ]), bval_Z]
    ring
  have hrun0 : BRun b4 ⟨z, .Rt, .P2 :: (w0 2 ++ [.R])⟩
      ⟨q, .Rt, .P1 :: [RB.Y, .Y, .V, .R]⟩ (0 + (2 + (0 + 2))) := by
    refine BRun.head (show bstep b4 ⟨z, .Rt, .P2 :: (w0 2 ++ [.R])⟩
      = some (⟨z, .Rt, RB.Y :: .P2 :: [RB.X, .Y, .Y, .V, .R]⟩, 0) from rfl) ?_
    refine BRun.head (show bstep b4 ⟨z, .Rt, RB.Y :: .P2 :: [RB.X, .Y, .Y, .V, .R]⟩
      = some (⟨.Z :: z, .Rt, .P2 :: [RB.X, .Y, .Y, .V, .R]⟩, 2) from rfl) ?_
    refine BRun.head (show bstep b4 ⟨.Z :: z, .Rt, .P2 :: [RB.X, .Y, .Y, .V, .R]⟩
      = some (⟨.Z :: z, .Rt, RB.V :: .P1 :: [RB.Y, .Y, .V, .R]⟩, 0) from rfl) ?_
    exact BRun.of_step (show bstep b4 ⟨.Z :: z, .Rt, RB.V :: .P1 :: [RB.Y, .Y, .V, .R]⟩
      = some (⟨q, .Rt, .P1 :: [RB.Y, .Y, .V, .R]⟩, 2) from rfl)
  refine SRet.of_run hrun0 ?_
  -- the pending decrement fails and the stack overflows
  obtain ⟨k₁, hrun₁⟩ := brun_overflow_of (b4 := b4) hstq hcvq (.Y :: .P2 :: [RB.Y, .V, .R])
  rw [ofw_eq_pdec hstq hcvq] at hrun₁
  refine SRet.of_run (BRun.head (show bstep b4 ⟨q, .Rt, .P1 :: [RB.Y, .Y, .V, .R]⟩
      = some (⟨q, .Rt, .U :: [RB.P2, .Y, .V, .R]⟩, 0) from rfl)
    (BRun.head (show bstep b4 ⟨q, .Rt, .U :: [RB.P2, .Y, .V, .R]⟩
        = some (⟨q, .Lt, RB.Y :: [RB.P2, .Y, .V, .R]⟩, 1) from rfl) hrun₁)) ?_
  refine SRet.of_step (show bstep b4 ⟨[LB.L], .Lt, pdec q ++ (RB.Y :: .P2 :: [RB.Y, .V, .R])⟩
    = some (⟨[LB.L], .Rt, .P2 :: (pdec q ++ (RB.Y :: .P2 :: [RB.Y, .V, .R]))⟩, 4) from rfl) ?_
  -- reset the deposited word and its extra one bit
  have hdigY : Digs (pdec q ++ [RB.Y]) := (pdec_digs q).append (digs_singleton (Or.inl rfl))
  have hbq : rrun (pdec q) 0 = bval q := (bval_eq_rrun q).symm
  have hbase : rrun (pdec q ++ [RB.Y]) 0 = 2 * bval q + 1 := by
    rw [rrun_append, hbq]
    simp
  have hclq : 0 ≤ rrun (pdec q ++ [RB.Y]) (cval ([LB.L] : List LB)) := by
    rw [hL]
    simpa [hbase] using by omega
  obtain ⟨p', phys, k, hrun, hstp, hpaid, hcvp⟩ :=
    brun_paid (b4 := b4) (pdec q ++ [RB.Y]) hdigY true [LB.L] CStack.base (by simp)
      (by simpa using hclq) (.P2 :: [RB.Y, .V, .R])
  obtain ⟨hstt, hadmt, hgt, hcvt, -, -⟩ :=
    tfold_props (pdec q ++ [RB.Y]) hdigY (σ := [LB.L]) CStack.base adm_L good_L
      (by simpa using hclq)
  set t : List LB := tfold [LB.L] (pdec q ++ [RB.Y]) with ht
  have hpaid' : paid p' phys = t := by simpa using hpaid
  have hcvt' : (cval t : ℤ) = 2 * bval q + 1 := by rw [hcvt, hL, Nat.cast_zero, hbase]
  have hx : 1 ≤ cval t := by
    have : (1 : ℤ) ≤ (cval t : ℤ) := by rw [hcvt']; omega
    exact_mod_cast this
  have hsplit : pdec q ++ (RB.Y :: .P2 :: [RB.Y, .V, .R])
      = (pdec q ++ [RB.Y]) ++ (.P2 :: [RB.Y, .V, .R]) := by simp
  rw [hsplit]
  refine SRet.of_run hrun ?_
  obtain ⟨k₂, hrun₂⟩ := brun_pd_push (b4 := b4) hstp (by
    intro hpf
    have := hcvp hpf
    omega) [RB.Y, .V, .R]
  rw [hpaid'] at hrun₂
  refine SRet.of_run hrun₂ ?_
  have hYV : ([RB.Y, RB.V] ++ [RB.R]) = [RB.Y, RB.V, RB.R] := rfl
  rw [← hYV]
  exact sret0_counter_drain hstt (DyckRun.consY (DyckRun.consV (DyckRun.nil 0)))
    (lemma_seven hgt hx).1 (lemma_seven hgt hx).2

/-! ## The branch -/

/-- **The `01` branch after the first pop**: the `01` branch met after the first pop always returns to
a `0RB` checkpoint. -/
theorem zevenS : ∀ (c : List LB) (w : List RB) (h : ℕ), CStack c → Adm c → Good c →
    Strict c → Gen w h → SRet b4 ⟨c, .Lt, .X :: .P2 :: (w ++ [.R])⟩ := by
  intro c w h hst hadm hg hstr hgen
  rcases Nat.eq_zero_or_pos (cval c) with h0 | h1
  · exact sret0_overflow_gen hst hadm hg hstr h0 (Or.inl rfl) (by simp) hgen
  · have hcv : cval (cdec c) = cval c - 1 := cdec_cval hst h1
    have hstd : CStack (cdec c) := cdec_CStack_all hst
    have hadmd : Adm (cdec c) := Adm.cdec hst hadm h1
    have hgd : Good (cdec c) := Good.cdec hst hg h1
    have hstrd : Strict (cdec c) := hstr.cdec hst h1
    obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.X :: .P2 :: (w ++ [.R]))
    have hs1 : bstep b4 ⟨cdec c, .Rt, .X :: .P2 :: (w ++ [.R])⟩
        = some (⟨cdec c, .Lt, .V :: .P2 :: (w ++ [.R])⟩, 1) := rfl
    refine SRet.of_run (hr1.trans (BRun.of_step hs1)) ?_
    rcases Nat.eq_zero_or_pos (cval (cdec c)) with h0' | h1'
    · refine sret0_overflow_gen hstd hadmd hgd hstrd h0' (Or.inr rfl) (fun _ => ?_) hgen
      rw [pdec_cdec hst h1]
      intro h00
      have hb := bal_pdec c
      rw [h00] at hb
      have hu := one_le_unmatched hst hadm h1
      have hah := hadm.head
      simp only [bal_nil] at hb
      omega
    · have hcv2 : cval (cdec (cdec c)) = cval (cdec c) - 1 := cdec_cval hstd h1'
      have hbv2 : bval (cdec (cdec c)) = bval (cdec c) := bval_cdec hstd h1'
      have hbv : bval (cdec c) = bval c := bval_cdec hst h1
      have hstd2 : CStack (cdec (cdec c)) := cdec_CStack_all hstd
      have hadmd2 : Adm (cdec (cdec c)) := Adm.cdec hstd hadmd h1'
      have hgd2 : Good (cdec (cdec c)) := Good.cdec hstd hgd h1'
      have hstrd2 : Strict (cdec (cdec c)) := hstrd.cdec hstd h1'
      obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.V :: .P2 :: (w ++ [.R]))
      have hs2 : bstep b4 ⟨cdec (cdec c), .Rt, .V :: .P2 :: (w ++ [.R])⟩
          = some (⟨.W :: cdec (cdec c), .Rt, .P2 :: (w ++ [.R])⟩, 2) := rfl
      refine SRet.of_run (hr2.trans (BRun.of_step hs2)) ?_
      -- the stack after the pop
      have h2c : 2 ≤ cval c := by omega
      have hcount : 2 ≤ nbit c - nsh c := two_le_unmatched hst hadm h2c
      have hadmh := hadm.head
      have hgh : (cval c : ℤ) ≤ bval c := hg.head
      have hcast : ((cval c - 2 : ℕ) : ℤ) = (cval c : ℤ) - 2 := by
        have : 2 ≤ (cval c : ℤ) := by exact_mod_cast h2c
        omega
      have hcv2' : cval (cdec (cdec c)) = cval c - 2 := by omega
      have hbv2' : bval (cdec (cdec c)) = bval c := by rw [hbv2, hbv]
      set τ : List LB := .W :: cdec (cdec c) with hτ
      have hstτ : CStack τ := hstd2.consW
      have hadmτ : Adm τ :=
        adm_consW hadmd2 (by rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]; omega)
      have hgτ : Good τ := good_consW hgd2 (by rw [hcv2', hbv2', hcast]; omega)
      have hstrτ : Strict τ :=
        strict_consW hstrd2 (by rw [nbit_cdec, nsh_cdec, nbit_cdec, nsh_cdec]; omega)
      by_cases hz : cval τ = 0
      · rcases eq_or_ne w (w0 2) with rfl | hne
        · exact sret0_exc hstτ hgτ hz
        · exact sret0_gen_reset hstτ hadmτ hgτ hstrτ hgen (Or.inl hne)
      · exact sret0_gen_reset hstτ hadmτ hgτ hstrτ hgen (Or.inr (by omega))

/-- `SRet` gives the base-level return predicate of `0RB`. -/
theorem SRet.ret0 {c : BCfg} (h : SRet b4 c) : Ret0 b4 c.den := by
  rcases h with ⟨s, k, hs, hrun⟩ | ⟨c', k, hs, hrun⟩
  · exact Or.inl ⟨s, k, hs.toCP0, hrun.sound⟩
  · exact Or.inr (hrun.not_halts hs.not_halts)

/-- **`ZEven` holds**: the `01` branch met after the first pop always returns to
a `0RB` checkpoint. -/
theorem zeven : ZEven := fun c w h hst hadm hg hstr hgen =>
  (zevenS (b4 := b4_0RB) c w h hst hadm hg hstr hgen).ret0

end BB25.Prefix
