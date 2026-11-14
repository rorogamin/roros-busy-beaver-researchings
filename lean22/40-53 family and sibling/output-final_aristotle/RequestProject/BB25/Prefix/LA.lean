/-
# The member `1LA`, and what its non-halting is reduced to

Its `A> 241` rule is

```
  A> 241  ⟶  <B1 22        (nine base steps)
```

so, unlike every member treated so far, the `141` block does **not** end the
`<B1` sweep: after the two decrements the head is back in state `<B1`, on the
stack `D²(c)`, with one more `22` block in front of it.  The sweep therefore
*continues*, and it can consume several pops in a row, each one costing two
decrements of the counter below it.

```
  c W <B1 …  ⟶  D²(c) <B1 22 …        (when cval c ≥ 2)
```

If some pop is met with a counter below two, the two excursions are not
available and the head meets the `241` block out of phase — which halts the
machine in three steps.  So for `1LA` goodness of the checkpoint is *not*
enough: what is needed is the extra, finite and decidable, property that the
whole scan of the current stack succeeds.  That property is `Ready` below; it
is exactly the "B scan" predicate of the submitted argument, and the
counterexample quoted there (`ZXZWWX`, good, positive and `X`-ending but not
ready) shows that it does not follow from the invariant of the other members.

This file formalises the part of the submitted argument that does not need the
new reset-to-`B` comparison lemma:

* the scan itself (`scan_1LA`): from a **ready** checkpoint the machine either
  runs off the left end in state `<B1` — the known spinout — or reaches the
  member-independent `01` branch of the sweep, with at least two `22` blocks in
  front of it;
* the blank-tape seed is a ready checkpoint (`readyCP_seed`);
* hence `1LA` never halts as soon as the `01` branch always returns to a ready
  checkpoint (`not_halts_1LA_of_zready`).

That last hypothesis, `ZReady`, is Sections 5–7 of the submitted document (the
exact word of a direct return, the reverse-debt interpreter and the dual-credit
comparison).  It is stated here as an explicit hypothesis, never as an axiom,
and it is **proved** in `RequestProject.BB25.Prefix.LA.Final` (`zready`), which
also derives the unconditional `not_halts_1LA` from the theorem below.
-/
import RequestProject.BB25.Prefix.Main
import RequestProject.BB25.Prefix.Strict

namespace BB25.Prefix

open BB25

/-! ## The rule and the scan predicate -/

/-- **The `<B1` scan of `1LA` succeeds.**  Reading the stack from the head
down, the scan strips zero bits, and at a pop it spends two decrements of the
counter below and carries on; it stops at a one bit (the member-independent
branch of the sweep) or at the left end (the spinout).  `Ready s` says that it
never meets a pop whose counter is below two. -/
inductive Ready : List LB → Prop
  | bottom : Ready [.L]
  | zero (t : List LB) : Ready (.Z :: t)
  | bit {t : List LB} : Ready t → Ready (.X :: t)
  | pop {t : List LB} : 2 ≤ cval t → Ready (cdec (cdec t)) → Ready (.W :: t)

theorem Ready.of_bit {t : List LB} (h : Ready (.X :: t)) : Ready t := by
  cases h with
  | bit h' => exact h'

/-- A checkpoint of `1LA`: a safe checkpoint whose scan succeeds. -/
structure ReadyCP (s : List LB) : Prop where
  cp : SafeCP s
  ready : Ready s
  strict : Strict s

/-- From `c` the machine either reaches a *ready* checkpoint or never halts. -/
def RReturns (b4 : Option (Sym × Dir × St)) (c : BCfg) : Prop :=
  (∃ (s : List LB) (k : ℕ), ReadyCP s ∧ BRun b4 c (cpCfg s) k) ∨ ¬ Halts (M b4) c.den

variable {b4 : Option (Sym × Dir × St)}

theorem RReturns.of_run {c c' : BCfg} {k : ℕ} (hr : BRun b4 c c' k) (h : RReturns b4 c') :
    RReturns b4 c := by
  rcases h with ⟨s, k', hs, hrun⟩ | hnh
  · exact Or.inl ⟨s, k + k', hs, hr.trans hrun⟩
  · exact Or.inr (hr.not_halts hnh)

/-- **The missing lemma of the submitted argument.**  The member-independent
`01` branch of the sweep — the head at `<A` in front of a `11` block, a pending
`2>` and a run of at least two `22` blocks — returns to a checkpoint that is
*ready* again.  Sections 5–7 of the submitted document prove this for `1LA`;
it is not formalised here. -/
def ZReady (b4 : Option (Sym × Dir × St)) : Prop :=
  ∀ (c : List LB) (r : ℕ), CStack c → Adm c → Good c → 2 ≤ r →
    RReturns b4 ⟨c, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩

/-! ## The scan -/

/-- **The `<B1` sweep of `1LA` on a ready stack.**  Every pop it meets has the
two decrements it needs, so the sweep ends either at the left end — the
spinout — or at a one bit, where the member-independent branch takes over. -/
theorem scan_1LA (hZ : ZReady b4_1LA) {s : List LB} (hrd : Ready s) :
    ∀ (r : ℕ), 2 ≤ r → CStack s → Adm s → Good s →
      RReturns b4_1LA ⟨s, .Bt, List.replicate r .Y ++ [.R1]⟩ := by
  induction hrd with
  | bottom =>
      intro r _ _ _ _
      exact Or.inr (not_halts_Bt_L _)
  | zero t =>
      intro r hr2 hst hadm hg
      have hst' : CStack t := by cases hst with | consZ h => exact h
      refine RReturns.of_run (BRun.of_step
        (show bstep b4_1LA ⟨.Z :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
          = some (⟨t, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩, 4) from rfl)) ?_
      exact hZ t r hst' (hadm.suffix (List.suffix_cons _ _))
        (hg.suffix (List.suffix_cons _ _)) hr2
  | @bit t hrd ih =>
      intro r hr2 hst hadm hg
      have hst' : CStack t := by cases hst with | consX h => exact h
      refine RReturns.of_run (BRun.of_step
        (show bstep b4_1LA ⟨.X :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
          = some (⟨t, .Bt, .Y :: (List.replicate r .Y ++ [.R1])⟩, 6) from rfl)) ?_
      rw [show RB.Y :: (List.replicate r RB.Y ++ [RB.R1])
        = List.replicate (r + 1) RB.Y ++ [RB.R1] by rw [List.replicate_succ, List.cons_append]]
      exact ih (r + 1) (by omega) hst' (hadm.suffix (List.suffix_cons _ _))
        (hg.suffix (List.suffix_cons _ _))
  | @pop t h2 hrd ih =>
      intro r hr2 hst hadm hg
      have hst' : CStack t := by cases hst with | consW h => exact h
      have hadm' : Adm t := hadm.suffix (List.suffix_cons _ _)
      have hg' : Good t := hg.suffix (List.suffix_cons _ _)
      have h1 : 1 ≤ cval t := by omega
      have hstd : CStack (cdec t) := cdec_CStack_all hst'
      have hcv : cval (cdec t) = cval t - 1 := cdec_cval hst' h1
      have h1' : 1 ≤ cval (cdec t) := by omega
      have hstd2 : CStack (cdec (cdec t)) := cdec_CStack_all hstd
      have hadmd2 : Adm (cdec (cdec t)) :=
        Adm.cdec hstd (Adm.cdec hst' hadm' h1) h1'
      have hgd2 : Good (cdec (cdec t)) :=
        Good.cdec hstd (Good.cdec hst' hg' h1) h1'
      set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
      obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_1LA) hst' h1 (.F :: tail)
      obtain ⟨k2, hr2'⟩ := brun_cdec_of (b4 := b4_1LA) hstd h1' (.G :: tail)
      refine RReturns.of_run (BRun.head
        (show bstep b4_1LA ⟨.W :: t, .Bt, tail⟩ = some (⟨t, .Lt, .F :: tail⟩, 2) from rfl)
        (hr1.trans (BRun.head
          (show bstep b4_1LA ⟨cdec t, .Rt, .F :: tail⟩
            = some (⟨cdec t, .Lt, .G :: tail⟩, 1) from rfl)
          (hr2'.trans (BRun.of_step
            (show bstep b4_1LA ⟨cdec (cdec t), .Rt, .G :: tail⟩
              = some (⟨cdec (cdec t), .Bt, .Y :: tail⟩, 9) from rfl)))))) ?_
      rw [htail, show RB.Y :: (List.replicate r RB.Y ++ [RB.R1])
        = List.replicate (r + 1) RB.Y ++ [RB.R1] by rw [List.replicate_succ, List.cons_append]]
      exact ih (r + 1) (by omega) hstd2 hadmd2 hgd2

/-! ## From a ready checkpoint to the next one -/

/-- One return of `1LA`, from a ready checkpoint: the first `11` block is
stripped at a cost of six base steps, and then the scan takes over. -/
theorem readyCP_returns (hZ : ZReady b4_1LA) {s : List LB} (h : ReadyCP s) :
    ∃ (c₁ : BCfg) (k₁ : ℕ), 1 ≤ k₁ ∧ BRun b4_1LA (cpCfg s) c₁ k₁ ∧ RReturns b4_1LA c₁ := by
  obtain ⟨t, rfl⟩ := h.cp.endX
  refine ⟨⟨t, .Bt, .Y :: (List.replicate 1 .Y ++ [.R1])⟩, 6, by omega,
    BRun.of_step rfl, ?_⟩
  rw [show RB.Y :: (List.replicate 1 RB.Y ++ [RB.R1])
    = List.replicate 2 RB.Y ++ [RB.R1] from rfl]
  have hst' : CStack t := by cases h.cp.st with | consX hh => exact hh
  exact scan_1LA hZ h.ready.of_bit 2 (by omega) hst'
    (h.cp.adm.suffix (List.suffix_cons _ _)) (h.cp.good.suffix (List.suffix_cons _ _))

theorem not_halts_of_readyCP (hZ : ZReady b4_1LA) :
    ∀ (n : ℕ) (s : List LB), ReadyCP s → steps (M b4_1LA) n (cpCfg s).den ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro s hs hn
      obtain ⟨c₁, k₁, hk₁, hrun₁, hret⟩ := readyCP_returns hZ hs
      obtain ⟨hlt₁, hn₁⟩ := halt_time_of_run hrun₁ hn
      rcases hret with ⟨s', k', hs', hrun'⟩ | hnh
      · obtain ⟨hlt', hn'⟩ := halt_time_of_run hrun' hn₁
        exact ih (n - k₁ - k') (by omega) s' hs' hn'
      · exact hnh ⟨n - k₁, hn₁⟩

/-! ## The blank-tape seed -/

/-- The seed checkpoint of the family is ready: its scan strips three `11`
blocks and stops at the first `01`. -/
theorem readyCP_seed : ReadyCP seedStack :=
  ⟨safeCP_seed, ((Ready.zero _).bit).bit.bit, strict_seedStack⟩

/-- **`1RB2LA0RB1LB---_1LA3RA1RA4LB1LA` never halts, granted `ZReady`.**  This
is the submitted argument minus its Sections 5–7: everything except the proof
that the `01` branch of the sweep returns to a stack whose scan succeeds. -/
theorem not_halts_1LA_of_zready (hZ : ZReady b4_1LA) : ¬ Halts (M b4_1LA) init := by
  rintro ⟨n, hn⟩
  have hlt : 156 < n := by
    by_contra hc
    exact not_halts_within (seed_run (b4 := b4_1LA)) n (by omega) hn
  have h2 : steps (M b4_1LA) (156 + (n - 156)) init = none := by
    rw [show 156 + (n - 156) = n by omega]
    exact hn
  rw [steps_add, seed_run] at h2
  simp only [Option.bind_some] at h2
  exact not_halts_of_readyCP hZ (n - 156) seedStack readyCP_seed h2

end BB25.Prefix
