/-
# The `<B1` sweep of `0RB`

From a `0RB` checkpoint the sweep strips zero bits and, at every pop, spends
two decrements and runs the marker episode of `Count.lean`.  Because the
checkpoint is *ready*, every pop it meets has its two decrements, so the sweep
is finite and ends either at the left end — the known spinout — or at a one
bit, where the head leaves the sweep with the word it has built in front of it.

The file reduces non-halting of `0RB` to the two `01` branches:

* `ZOdd`: the branch met before the first pop, where the right word is still a
  run of `22` blocks over the terminal `1$`.  This is the branch of every other
  member of the family.
* `ZEven`: the branch met after the first pop, where the right word is a
  generated word over the bare right end.

In between sits `first_episode`, the first pop: it turns the run of `r` `22`
blocks into the base word `w0 r` over the bare right end.  Its three cases are
the number `r - 2` of one bits the sweep leaves above the marker.
-/
import RequestProject.BB25.Prefix.RB.Gen

namespace BB25.Prefix

open BB25

/-! ## The two `01` branches -/

/-- The `01` branch before the first pop. -/
def ZOdd : Prop :=
  ∀ (c : List LB) (r : ℕ), CStack c → Adm c → Good c → Strict c → 2 ≤ r →
    Ret0 b4_0RB (⟨c, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩ : BCfg).den

/-- The `01` branch after the first pop. -/
def ZEven : Prop :=
  ∀ (c : List LB) (w : List RB) (h : ℕ), CStack c → Adm c → Good c → Strict c → Gen w h →
    Ret0 b4_0RB (⟨c, .Lt, .X :: .P2 :: (w ++ [.R])⟩ : BCfg).den

/-! ## The re-parsing of a pending digit at the right end -/

/-- The two block words of the base word `w0 2`, before and after the
re-parsing of the pending digit. -/
theorem den_w0_two (c : List LB) :
    (⟨c, .Bt, RB.Y :: .X :: .P2 :: [.Y, .Y, .R1]⟩ : BCfg).den
      = (⟨c, .Bt, w0 2 ++ [.R]⟩ : BCfg).den := rfl

theorem den_w0_three (c : List LB) :
    (⟨c, .Bt, RB.Y :: .Y :: .V :: .P2 :: [.Y, .Y, .R1]⟩ : BCfg).den
      = (⟨c, .Bt, w0 3 ++ [.R]⟩ : BCfg).den := rfl

/-! ## The first pop -/

/-- **The first pop of the sweep.**  The head meets a pop with a run of `r`
`22` blocks and the terminal `1$` in front of it; it comes back to the sweep
two decrements lower, with the base word `w0 r` over the bare right end. -/
theorem first_episode {c : List LB} (hst : CStack c) (h2 : 2 ≤ cval c) {r : ℕ} (hr : 2 ≤ r)
    (hcont : Ret0 b4_0RB (⟨cdec (cdec c), .Bt, w0 r ++ [.R]⟩ : BCfg).den) :
    Ret0 b4_0RB (⟨.W :: c, .Bt, List.replicate r .Y ++ [.R1]⟩ : BCfg).den := by
  have h1 : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcvd : cval (cdec c) = cval c - 1 := cdec_cval hst h1
  have h1' : 1 ≤ cval (cdec c) := by omega
  set c2 : List LB := cdec (cdec c) with hc2
  set β : List LB := .J0 :: c2 with hβ
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  -- two decrements and the `A> 241` rule create the marker
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_0RB) hst h1 (.F :: tail)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_0RB) hstd h1' (.G :: tail)
  refine Ret0.of_step (show bstep b4_0RB ⟨.W :: c, .Bt, tail⟩
      = some (⟨c, .Lt, .F :: tail⟩, 2) from rfl) ?_
  refine Ret0.of_run hr1 (Ret0.of_step (show bstep b4_0RB ⟨cdec c, .Rt, .F :: tail⟩
      = some (⟨cdec c, .Lt, .G :: tail⟩, 1) from rfl) ?_)
  refine Ret0.of_run hr2 (Ret0.of_step (show bstep b4_0RB ⟨c2, .Rt, .G :: tail⟩
      = some (⟨β, .Rt, tail⟩, 3) from rfl) ?_)
  -- the head builds the local counter and turns at the right end
  refine Ret0.of_run (brun_Yrun (b4 := b4_0RB) r β [.R1]) ?_
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  set p : List LB := List.replicate (j + 2) .Z ++ [.L] with hp
  have hstp : CStack p := CStack_Zrun _ CStack.base
  have hcvp : cval p = 2 ^ (j + 2) - 1 := by rw [hp, cval_Zrun]; simp
  have hpow : 4 ≤ 2 ^ (j + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrep : rep β p = List.replicate (j + 2) .Z ++ β := by rw [hp, rep_Zrun, rep_L]
  have hcvp1 : 1 ≤ cval p := by omega
  obtain ⟨k3, hr3⟩ := brun_cdec_rep_of (b4 := b4_0RB) (β := β) hstp hcvp1 [.R2]
  rw [← hrep]
  refine Ret0.of_step (show bstep b4_0RB ⟨rep β p, .Rt, [RB.R1]⟩
      = some (⟨rep β p, .Lt, [.R2]⟩, 1) from rfl) ?_
  refine Ret0.of_run hr3 ?_
  have hcdecp : cdec p = .X :: (List.replicate (j + 1) .Z ++ [.L]) := by
    rw [hp, List.replicate_succ, List.cons_append, cdec_Z]
  rw [hcdecp]
  refine Ret0.of_step (show bstep b4_0RB ⟨rep β (.X :: (List.replicate (j + 1) .Z ++ [.L])),
      .Rt, [RB.R2]⟩ = some (⟨rep β (.X :: (List.replicate (j + 1) .Z ++ [.L])),
        .Bt, [.Y, .R1]⟩, 11) from rfl) ?_
  rw [show rep β (.X :: (List.replicate (j + 1) .Z ++ [.L]))
    = .X :: rep β (List.replicate (j + 1) .Z ++ [.L]) from rfl]
  refine Ret0.of_step (show bstep b4_0RB ⟨.X :: rep β (List.replicate (j + 1) .Z ++ [.L]),
      .Bt, [RB.Y, .R1]⟩
      = some (⟨rep β (List.replicate (j + 1) .Z ++ [.L]), .Bt, [.Y, .Y, .R1]⟩, 6) from rfl) ?_
  rw [show rep β (List.replicate (j + 1) .Z ++ [.L])
    = .Z :: rep β (List.replicate j .Z ++ [.L]) by
      rw [List.replicate_succ, List.cons_append]; rfl]
  refine Ret0.of_step (show bstep b4_0RB ⟨.Z :: rep β (List.replicate j .Z ++ [.L]),
      .Bt, [RB.Y, .Y, .R1]⟩
      = some (⟨rep β (List.replicate j .Z ++ [.L]), .Lt, [.X, .P2, .Y, .Y, .R1]⟩, 4) from rfl) ?_
  rw [show rep β (List.replicate j .Z ++ [.L]) = List.replicate j .Z ++ β by
    rw [rep_Zrun, rep_L]]
  -- the three cases of the local episode
  match j with
  | 0 =>
      refine Ret0.of_step (show bstep b4_0RB ⟨β, .Lt, [RB.X, .P2, .Y, .Y, .R1]⟩
        = some (⟨c2, .Bt, .Y :: [RB.X, .P2, .Y, .Y, .R1]⟩, 9) from rfl) ?_
      simpa using Ret0.of_den (den_w0_two c2) hcont
  | 1 =>
      refine Ret0.of_step (show bstep b4_0RB
        ⟨List.replicate 1 LB.Z ++ β, .Lt, [RB.X, .P2, .Y, .Y, .R1]⟩
        = some (⟨.X :: β, .Rt, [RB.X, .P2, .Y, .Y, .R1]⟩, 3) from rfl) ?_
      refine Ret0.of_step (show bstep b4_0RB ⟨.X :: β, .Rt, [RB.X, .P2, .Y, .Y, .R1]⟩
        = some (⟨.X :: β, .Lt, [RB.V, .P2, .Y, .Y, .R1]⟩, 1) from rfl) ?_
      refine Ret0.of_step (show bstep b4_0RB ⟨.X :: β, .Lt, [RB.V, .P2, .Y, .Y, .R1]⟩
        = some (⟨β, .Lt, [RB.Y, .V, .P2, .Y, .Y, .R1]⟩, 2) from rfl) ?_
      refine Ret0.of_step (show bstep b4_0RB ⟨β, .Lt, [RB.Y, .V, .P2, .Y, .Y, .R1]⟩
        = some (⟨c2, .Bt, .Y :: [RB.Y, .V, .P2, .Y, .Y, .R1]⟩, 9) from rfl) ?_
      simpa using Ret0.of_den (den_w0_three c2) hcont
  | (k + 2) =>
      refine marker_drain_gen (b4 := b4_0RB) (β := β) k
        (P := fun cfg => Ret0 b4_0RB cfg.den) (fun hrun h => Ret0.of_run hrun h) ?_
      refine Ret0.of_step (show bstep b4_0RB ⟨β, .Lt, kword (k + 2) ++ [RB.R]⟩
        = some (⟨c2, .Bt, .Y :: (kword (k + 2) ++ [RB.R])⟩, 9) from rfl) ?_
      have hw : RB.Y :: (kword (k + 2) ++ [RB.R]) = w0 (k + 4) ++ [RB.R] := by
        rw [w0_big]
        rfl
      rw [hw]
      exact hcont

/-! ## The sweep -/

/-- **The sweep after the first pop.**  The right word is a generated word over
the bare right end. -/
theorem sweep_even (hZ : ZEven) : ∀ {s : List LB}, Ready s → ∀ (w : List RB) (h : ℕ), Gen w h →
    CStack s → Adm s → Good s → Strict s →
    Ret0 b4_0RB (⟨s, .Bt, w ++ [.R]⟩ : BCfg).den := by
  intro s hrd
  induction hrd with
  | bottom =>
      intro w h _ _ _ _ _
      exact Or.inr (not_halts_Bt_L _)
  | zero t =>
      intro w h hg hst hadm hg' hstr
      have hst' : CStack t := by cases hst with | consZ hh => exact hh
      refine Ret0.of_step (show bstep b4_0RB ⟨.Z :: t, .Bt, w ++ [.R]⟩
        = some (⟨t, .Lt, .X :: .P2 :: (w ++ [.R])⟩, 4) from rfl) ?_
      exact hZ t w h hst' (hadm.suffix (List.suffix_cons _ _))
        (hg'.suffix (List.suffix_cons _ _)) (hstr.suffix (List.suffix_cons _ _)) hg
  | @bit t hrd ih =>
      intro w h hg hst hadm hg' hstr
      have hst' : CStack t := by cases hst with | consX hh => exact hh
      refine Ret0.of_step (show bstep b4_0RB ⟨.X :: t, .Bt, w ++ [.R]⟩
        = some (⟨t, .Bt, .Y :: (w ++ [.R])⟩, 6) from rfl) ?_
      have he : RB.Y :: (w ++ [RB.R]) = (RB.Y :: w) ++ [RB.R] := rfl
      rw [he]
      exact ih (.Y :: w) (h + 1) hg.pre hst' (hadm.suffix (List.suffix_cons _ _))
        (hg'.suffix (List.suffix_cons _ _)) (hstr.suffix (List.suffix_cons _ _))
  | @pop t hv hrd ih =>
      intro w h hg hst hadm hg' hstr
      have hst' : CStack t := by cases hst with | consW hh => exact hh
      have hadm' : Adm t := hadm.suffix (List.suffix_cons _ _)
      have hgt : Good t := hg'.suffix (List.suffix_cons _ _)
      have hstrt : Strict t := hstr.suffix (List.suffix_cons _ _)
      have h1 : 1 ≤ cval t := by omega
      have hstd : CStack (cdec t) := cdec_CStack_all hst'
      have hcvd : cval (cdec t) = cval t - 1 := cdec_cval hst' h1
      have h1' : 1 ≤ cval (cdec t) := by omega
      obtain ⟨k, hrun⟩ := rb_pop_episode hst' hv hg.dyck
      refine Ret0.of_run hrun ?_
      exact ih _ 0 hg.mark (cdec_CStack_all hstd) (Adm.cdec hstd (Adm.cdec hst' hadm' h1) h1')
        (Good.cdec hstd (Good.cdec hst' hgt h1) h1')
        ((hstrt.cdec hst' h1).cdec hstd h1')

/-- **The sweep before the first pop.** -/
theorem sweep_odd (hZo : ZOdd) (hZe : ZEven) : ∀ {s : List LB}, Ready s → ∀ (r : ℕ), 2 ≤ r →
    CStack s → Adm s → Good s → Strict s →
    Ret0 b4_0RB (⟨s, .Bt, List.replicate r .Y ++ [.R1]⟩ : BCfg).den := by
  intro s hrd
  induction hrd with
  | bottom =>
      intro r _ _ _ _ _
      exact Or.inr (not_halts_Bt_L _)
  | zero t =>
      intro r hr hst hadm hg hstr
      have hst' : CStack t := by cases hst with | consZ hh => exact hh
      refine Ret0.of_step (show bstep b4_0RB ⟨.Z :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
        = some (⟨t, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩, 4) from rfl) ?_
      exact hZo t r hst' (hadm.suffix (List.suffix_cons _ _))
        (hg.suffix (List.suffix_cons _ _)) (hstr.suffix (List.suffix_cons _ _)) hr
  | @bit t hrd ih =>
      intro r hr hst hadm hg hstr
      have hst' : CStack t := by cases hst with | consX hh => exact hh
      refine Ret0.of_step (show bstep b4_0RB ⟨.X :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
        = some (⟨t, .Bt, .Y :: (List.replicate r .Y ++ [.R1])⟩, 6) from rfl) ?_
      rw [show RB.Y :: (List.replicate r RB.Y ++ [RB.R1])
        = List.replicate (r + 1) RB.Y ++ [RB.R1] by rw [List.replicate_succ, List.cons_append]]
      exact ih (r + 1) (by omega) hst' (hadm.suffix (List.suffix_cons _ _))
        (hg.suffix (List.suffix_cons _ _)) (hstr.suffix (List.suffix_cons _ _))
  | @pop t hv hrd ih =>
      intro r hr hst hadm hg hstr
      have hst' : CStack t := by cases hst with | consW hh => exact hh
      have hadm' : Adm t := hadm.suffix (List.suffix_cons _ _)
      have hgt : Good t := hg.suffix (List.suffix_cons _ _)
      have hstrt : Strict t := hstr.suffix (List.suffix_cons _ _)
      have h1 : 1 ≤ cval t := by omega
      have hstd : CStack (cdec t) := cdec_CStack_all hst'
      have hcvd : cval (cdec t) = cval t - 1 := cdec_cval hst' h1
      have h1' : 1 ≤ cval (cdec t) := by omega
      refine first_episode hst' hv hr ?_
      exact sweep_even hZe hrd (w0 r) (h0 r) (Gen.base hr) (cdec_CStack_all hstd)
        (Adm.cdec hstd (Adm.cdec hst' hadm' h1) h1')
        (Good.cdec hstd (Good.cdec hst' hgt h1) h1')
        ((hstrt.cdec hst' h1).cdec hstd h1')

/-! ## Non-halting -/

/-- One return of `0RB` from a checkpoint: the first zero bit is stripped at a
cost of six base steps, and then the sweep takes over. -/
theorem cp0_returns (hZo : ZOdd) (hZe : ZEven) {s : List LB} (h : CP0 s) :
    ∃ (c₁ : BCfg) (k₁ : ℕ), 1 ≤ k₁ ∧ BRun b4_0RB (cpCfg s) c₁ k₁ ∧ Ret0 b4_0RB c₁.den := by
  obtain ⟨t, rfl⟩ := h.cp.endX
  refine ⟨⟨t, .Bt, .Y :: (List.replicate 1 .Y ++ [.R1])⟩, 6, by omega, BRun.of_step rfl, ?_⟩
  rw [show RB.Y :: (List.replicate 1 RB.Y ++ [RB.R1]) = List.replicate 2 RB.Y ++ [RB.R1] from rfl]
  have hst' : CStack t := by cases h.cp.st with | consX hh => exact hh
  exact sweep_odd hZo hZe h.ready.of_bit 2 (by omega) hst'
    (h.cp.adm.suffix (List.suffix_cons _ _)) (h.cp.good.suffix (List.suffix_cons _ _))
    (h.strict.suffix (List.suffix_cons _ _))

theorem not_halts_of_CP0 (hZo : ZOdd) (hZe : ZEven) :
    ∀ (n : ℕ) (s : List LB), CP0 s → steps (M b4_0RB) n (cpCfg s).den ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro s hs hn
      obtain ⟨c₁, k₁, hk₁, hrun₁, hret⟩ := cp0_returns hZo hZe hs
      obtain ⟨hlt₁, hn₁⟩ := halt_time_of_run hrun₁ hn
      rcases hret with ⟨s', k', hs', hst'⟩ | hnh
      · obtain ⟨hlt', hn'⟩ := halt_time_of_steps hst' hn₁
        exact ih (n - k₁ - k') (by omega) s' hs' hn'
      · exact hnh ⟨n - k₁, hn₁⟩

end BB25.Prefix
