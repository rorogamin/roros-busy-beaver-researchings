/-
# The sibling `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` never halts

The sibling has exactly the checkpoint dynamics of the `0RB` member: from a
`0RB` checkpoint (`CP0`, unchanged) its `<B1` sweep strips zero bits, handles
every pop with the sibling pop (`Pop.lean`), which spends the same two
decrements and produces the same word as the `0RB` pop, and stops either at
the left end (a spinout) or at a one bit, where the two `01` branches of
`zreadyS` and `zevenS` (proved in `Prefix/LA/Final.lean` and `Prefix/RB/Even.lean` for every `b4`, used here at `b4 = none`) take over.  The blank tape reaches the `0RB` seed checkpoint after
`156` steps.
-/
import RequestProject.BB25.Sibling.Pop

namespace BB25.Sibling

open BB25 BB25.Prefix

/-! ## Returns of the sibling -/

/-- From the base configuration `c` the sibling either reaches a `0RB`
checkpoint or never halts. -/
def SRetM (c : Cfg) : Prop :=
  (∃ (s : List LB) (k : ℕ), CP0 s ∧ steps machine k c = some (cpCfg s).den) ∨
    ¬ Halts machine c

theorem not_halts_of_steps {c c' : Cfg} {k : ℕ} (hr : steps machine k c = some c')
    (h : ¬ Halts machine c') : ¬ Halts machine c := by
  rintro ⟨n, hn⟩
  apply h
  refine ⟨n - k, ?_⟩
  by_cases hkn : k ≤ n
  · have h2 : steps machine (k + (n - k)) c = none := by
      rw [show k + (n - k) = n by omega]; exact hn
    rw [steps_add, hr] at h2
    simpa using h2
  · exact absurd hn (not_halts_within hr n (by omega))

theorem SRetM.of_steps {c c' : Cfg} {k : ℕ} (hr : steps machine k c = some c')
    (h : SRetM c') : SRetM c := by
  rcases h with ⟨s, k', hs, hst⟩ | hnh
  · exact Or.inl ⟨s, k + k', hs, steps_trans hr hst⟩
  · exact Or.inr (not_halts_of_steps hr hnh)

/-! ## The spinouts -/

theorem xy_iter (t : List Sym) : ∀ j : ℕ,
    steps machine (9 * j) ⟨[1, 1], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩
      = some ⟨[1, 1], .A, .L, 1 :: 1 :: 2 :: 2 :: (List.replicate j 2 ++ t)⟩ := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show 9 * (j + 1) = 9 * j + 9 by ring]
      refine steps_trans ih ?_
      rw [xy_spinout_step, List.replicate_succ]
      rfl

/-- The left-end spinout reached by an exhausted counter. -/
theorem not_halts_spin {c : BCfg} (h : SpinCfg c) : ¬ Halts machine c.den := by
  obtain ⟨rest, rfl, -⟩ := h
  rintro ⟨n, hn⟩
  exact not_halts_within (xy_iter (2 :: denR rest) n) n (by omega) hn

theorem left_iter (t : List Sym) : ∀ j : ℕ,
    steps machine (8 * j) ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: t⟩
      = some ⟨[], .A, .L, 1 :: 1 :: 2 :: 2 :: (List.replicate (2 * j) 2 ++ t)⟩ := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show 8 * (j + 1) = 8 * j + 8 by ring]
      refine steps_trans ih ?_
      rw [spinout_step, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ,
        List.replicate_succ]
      rfl

/-- The head reaching the left end in the sweep. -/
theorem not_halts_Bt_L_sib (rt : List RB) : ¬ Halts machine (⟨[.L], .Bt, rt⟩ : BCfg).den := by
  refine not_halts_of_steps (leftend_B1_run (denR rt)) ?_
  rintro ⟨n, hn⟩
  exact not_halts_within (left_iter (denR rt) n) n (by omega) hn

/-- **The returns of the `01` branches transfer to the sibling.** -/
theorem _root_.BB25.Prefix.SRet.sib {c : BCfg} (h : SRet none c) (h0 : fgc c.rt = 0) : SRetM c.den := by
  rcases h with ⟨s, k, hs, hrun⟩ | ⟨c', k, hs, hrun⟩
  · exact Or.inl ⟨s, k, hs.toCP0, hrun.sib h0 rfl⟩
  · have h1 : fgc c'.rt = 0 := by
      obtain ⟨rest, rfl, hr⟩ := hs
      simpa using hr
    exact Or.inr (not_halts_of_steps (hrun.sib h0 h1) (not_halts_spin hs))

/-- A block step of the sibling other than a pop. -/
theorem step_sib {c c' : BCfg} {k : ℕ} (hs : bstep none c = some (c', k))
    (h0 : fgc c.rt = 0) (h1 : fgc c'.rt = 0) : steps machine k c.den = some c'.den :=
  (BRun.of_step hs).sib h0 h1

/-! ## The sweep -/

/-- **The sweep after the first pop.** -/
theorem sweep_even_sib : ∀ {s : List LB}, Ready s → ∀ (w : List RB) (h : ℕ), Gen w h →
    CStack s → Adm s → Good s → Strict s →
    SRetM (⟨s, .Bt, w ++ [.R]⟩ : BCfg).den := by
  intro s hrd
  induction hrd with
  | bottom =>
      intro w h _ _ _ _ _
      exact Or.inr (not_halts_Bt_L_sib _)
  | zero t =>
      intro w h hg hst hadm hg' hstr
      have hst' : CStack t := by cases hst with | consZ hh => exact hh
      have hfw : fgc w = 0 := fgc_digs hg.digs
      refine SRetM.of_steps (step_sib (show bstep none ⟨.Z :: t, .Bt, w ++ [.R]⟩
        = some (⟨t, .Lt, .X :: .P2 :: (w ++ [.R])⟩, 4) from rfl)
        (by simp [fgc_append, hfw]) (by simp [fgc_append, hfw])) ?_
      exact (zevenS (b4 := none) t w h hst' (hadm.suffix (List.suffix_cons _ _))
        (hg'.suffix (List.suffix_cons _ _)) (hstr.suffix (List.suffix_cons _ _)) hg).sib
        (by simp [fgc_append, hfw])
  | @bit t hrd ih =>
      intro w h hg hst hadm hg' hstr
      have hst' : CStack t := by cases hst with | consX hh => exact hh
      have hfw : fgc w = 0 := fgc_digs hg.digs
      refine SRetM.of_steps (step_sib (show bstep none ⟨.X :: t, .Bt, w ++ [.R]⟩
        = some (⟨t, .Bt, .Y :: (w ++ [.R])⟩, 6) from rfl)
        (by simp [fgc_append, hfw]) (by simp [fgc_append, hfw])) ?_
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
      obtain ⟨k, hrun⟩ := sib_pop_word hst' hv hg.dyck
      refine SRetM.of_steps hrun ?_
      exact ih _ 0 hg.mark (cdec_CStack_all hstd) (Adm.cdec hstd (Adm.cdec hst' hadm' h1) h1')
        (Good.cdec hstd (Good.cdec hst' hgt h1) h1')
        ((hstrt.cdec hst' h1).cdec hstd h1')

/-- **The sweep before the first pop.** -/
theorem sweep_odd_sib : ∀ {s : List LB}, Ready s → ∀ (r : ℕ), 2 ≤ r →
    CStack s → Adm s → Good s → Strict s →
    SRetM (⟨s, .Bt, List.replicate r .Y ++ [.R1]⟩ : BCfg).den := by
  intro s hrd
  induction hrd with
  | bottom =>
      intro r _ _ _ _ _
      exact Or.inr (not_halts_Bt_L_sib _)
  | zero t =>
      intro r hr hst hadm hg hstr
      have hst' : CStack t := by cases hst with | consZ hh => exact hh
      refine SRetM.of_steps (step_sib (show bstep none ⟨.Z :: t, .Bt,
          List.replicate r .Y ++ [.R1]⟩
        = some (⟨t, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩, 4) from rfl)
        (by simp [fgc_append, fgc_replicate]) (by simp [fgc_append, fgc_replicate])) ?_
      exact (zreadyS (b4 := none) t r hst' (hadm.suffix (List.suffix_cons _ _))
        (hg.suffix (List.suffix_cons _ _)) hr).sib (by simp [fgc_append, fgc_replicate])
  | @bit t hrd ih =>
      intro r hr hst hadm hg hstr
      have hst' : CStack t := by cases hst with | consX hh => exact hh
      refine SRetM.of_steps (step_sib (show bstep none ⟨.X :: t, .Bt,
          List.replicate r .Y ++ [.R1]⟩
        = some (⟨t, .Bt, .Y :: (List.replicate r .Y ++ [.R1])⟩, 6) from rfl)
        (by simp [fgc_append, fgc_replicate]) (by simp [fgc_append, fgc_replicate])) ?_
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
      obtain ⟨k, hrun⟩ := sib_first_pop hst' hv hr
      refine SRetM.of_steps hrun ?_
      exact sweep_even_sib hrd (w0 r) (h0 r) (Gen.base hr) (cdec_CStack_all hstd)
        (Adm.cdec hstd (Adm.cdec hst' hadm' h1) h1')
        (Good.cdec hstd (Good.cdec hst' hgt h1) h1')
        ((hstrt.cdec hst' h1).cdec hstd h1')

/-! ## Non-halting -/

/-- **One return of the sibling from a `0RB` checkpoint**, in at least six
base steps. -/
theorem cp0_returns_sib {s : List LB} (h : CP0 s) :
    ∃ (c₁ : Cfg) (k₁ : ℕ), 1 ≤ k₁ ∧ steps machine k₁ (cpCfg s).den = some c₁ ∧ SRetM c₁ := by
  obtain ⟨t, rfl⟩ := h.cp.endX
  have hst' : CStack t := by cases h.cp.st with | consX hh => exact hh
  refine ⟨(⟨t, .Bt, List.replicate 2 .Y ++ [.R1]⟩ : BCfg).den, 6, by omega,
    step_sib (show bstep none (cpCfg (.X :: t))
      = some (⟨t, .Bt, List.replicate 2 .Y ++ [.R1]⟩, 6) from rfl) rfl rfl, ?_⟩
  exact sweep_odd_sib h.ready.of_bit 2 (by omega) hst'
    (h.cp.adm.suffix (List.suffix_cons _ _)) (h.cp.good.suffix (List.suffix_cons _ _))
    (h.strict.suffix (List.suffix_cons _ _))

theorem halt_time_sib {c c' : Cfg} {k n : ℕ} (hr : steps machine k c = some c')
    (hn : steps machine n c = none) : k < n ∧ steps machine (n - k) c' = none := by
  have hlt : k < n := by
    by_contra hc
    exact not_halts_within hr n (by omega) hn
  refine ⟨hlt, ?_⟩
  have h2 : steps machine (k + (n - k)) c = none := by
    rw [show k + (n - k) = n by omega]
    exact hn
  rw [steps_add, hr] at h2
  simpa using h2

theorem not_halts_of_CP0_sib :
    ∀ (n : ℕ) (s : List LB), CP0 s → steps machine n (cpCfg s).den ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro s hs hn
      obtain ⟨c₁, k₁, hk₁, hrun₁, hret⟩ := cp0_returns_sib hs
      obtain ⟨hlt₁, hn₁⟩ := halt_time_sib hrun₁ hn
      rcases hret with ⟨s', k', hs', hst'⟩ | hnh
      · obtain ⟨hlt', hn'⟩ := halt_time_sib hst' hn₁
        exact ih (n - k₁ - k') (by omega) s' hs' hn'
      · exact hnh ⟨n - k₁, hn₁⟩

/-- **The sibling `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` never halts** from the
blank tape. -/
theorem not_halts_sibling : ¬ Halts machine init := by
  rintro ⟨n, hn⟩
  obtain ⟨-, hn'⟩ := halt_time_sib seed_run hn
  exact not_halts_of_CP0_sib (n - 156) seedStack cp0_seed hn'

end BB25.Sibling
