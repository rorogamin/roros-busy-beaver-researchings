/-
# The return theorem

A **safe checkpoint** is a configuration `L s <B1 22 1$` whose left stack `s`
is a good admissible counter stack with a positive counter (`SafeCP`).

From a safe checkpoint the `<B1` sweep strips the zero bits of the counter and
then meets either a one bit — which is the member-independent branch, settled
by `returns_dP2` of `Drain.lean` — or a pop, which creates the `141` block and
leads to the member-specific `A> 241` rule.

That second branch is abstracted here as `WCase b4`: the statement that the
machine returns from `L c <A 141 22…1$` whenever the counter stack `c` below
the pop is good with a counter of at least two.  Granting it, the machine never
halts from a safe checkpoint (`not_halts_of_safeCP`).

`WCase` is verified here for the members whose `A> 241` rule leaves a bit block
and a pending `2>` behind (`3RA` and `2LA`, via `GBit`); the remaining members
are treated in the files `Bit.lean` (`1RA`), `Zero.lean` (`0LA`) and
`Two.lean` (`2LB`).
-/
import RequestProject.BB25.Prefix.Drain

namespace BB25.Prefix

open BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## The member-specific branch of the sweep -/

/-- **The `141` block, created by a pop in the `<B1` sweep.**  Below the pop
sits a good counter stack `c` with `cval c ≥ 2`, so two decrements are
available before the head reaches the `241` block and the member-specific rule
fires.  The extra hypotheses `cval c = 2 → 4 ≤ bval c` and, more generally,
`cval c` even `→ cval c + 2 ≤ bval c` record what the goodness of the stack
`W :: c` at the checkpoint gives in the critical cases. -/
def WCase (b4 : Option (Sym × Dir × St)) : Prop :=
  ∀ (c : List LB) (r : ℕ), CStack c → Adm c → Good c → 2 ≤ cval c →
    (cval c = 2 → 4 ≤ bval c) → (cval c % 2 = 0 → (cval c : ℤ) + 2 ≤ bval c) → 2 ≤ r →
    Returns b4 ⟨c, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩

/-! ## The members whose `A> 241` rule leaves a bit block -/

/-- The property of the `A> 241` rule that this branch uses: the rule erases
the `241` block after two decrements and leaves a bit block and a pending `2>`
behind.  It holds for `3RA` (with `X`) and for `2LA` (with `Y`). -/
def GBit (b4 : Option (Sym × Dir × St)) (d : RB) (k : ℕ) : Prop :=
  ∀ (lt : List LB) (rest : List RB),
    gStep b4 lt rest = some (⟨lt, .Lt, d :: .P2 :: rest⟩, k)

theorem gBit_3RA : GBit b4_3RA .X 5 := fun _ _ => rfl
theorem gBit_2LA : GBit b4_2LA .Y 7 := fun _ _ => rfl

/-- Two decrements bring the head to the `241` block; the rule of the member
then leaves a bit block and a pending `2>`. -/
theorem wcase_of_gBit {d : RB} {kG : ℕ} (hG : GBit b4 d kG) (hd : d = RB.X ∨ d = RB.Y) :
    WCase b4 := by
  intro t r hst hadm hg hv _ _ hr2
  have hr : 1 ≤ r := by omega
  set tail : List RB := List.replicate r RB.Y ++ [RB.R1] with htail
  have h1 : 1 ≤ cval t := by omega
  have hcv : cval (cdec t) = cval t - 1 := cdec_cval hst h1
  have hstd : CStack (cdec t) := cdec_CStack_all hst
  have hadmd : Adm (cdec t) := Adm.cdec hst hadm h1
  have hgd : Good (cdec t) := Good.cdec hst hg h1
  have h1' : 1 ≤ cval (cdec t) := by omega
  have hstd2 : CStack (cdec (cdec t)) := cdec_CStack_all hstd
  have hadmd2 : Adm (cdec (cdec t)) := Adm.cdec hstd hadmd h1'
  have hgd2 : Good (cdec (cdec t)) := Good.cdec hstd hgd h1'
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4) hst h1 (.F :: tail)
  have hsF : bstep b4 ⟨cdec t, .Rt, .F :: tail⟩ = some (⟨cdec t, .Lt, .G :: tail⟩, 1) := rfl
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4) hstd h1' (.G :: tail)
  have hsG : bstep b4 ⟨cdec (cdec t), .Rt, .G :: tail⟩
      = some (⟨cdec (cdec t), .Lt, d :: .P2 :: tail⟩, kG) := hG _ _
  refine Returns.of_run
    (hr1.trans (BRun.head hsF (hr2.trans (BRun.of_step hsG)))) ?_
  exact returns_dP2 hstd2 hadmd2 hgd2 hd (Or.inl hr)

/-! ## The `<B1` sweep -/

/-- **The `<B1` sweep.**  The head strips the zero bits of the counter and then
meets a one bit or a pop. -/
private theorem returns_Bt_aux (hW : WCase b4) :
    ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → Adm s → Good s → 1 ≤ cval s →
      ∀ r : ℕ, 2 ≤ r → Returns b4 ⟨s, .Bt, List.replicate r .Y ++ [.R1]⟩ := by
  intro n
  induction n with
  | zero =>
      intro s hlen _ _ _ hv
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simp at hv
  | succ n ih =>
      intro s hlen hst hadm hg hv r hr
      match s with
      | [] => simp at hv
      | .L :: t => simp at hv
      | .X :: t =>
          have hst' : CStack t := by cases hst with | consX h => exact h
          have hv' : 1 ≤ cval t := by simp at hv; omega
          have hs1 : bstep b4 ⟨.X :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
              = some (⟨t, .Bt, .Y :: (List.replicate r .Y ++ [.R1])⟩, 6) := rfl
          refine Returns.of_run (BRun.of_step hs1) ?_
          have he : RB.Y :: (List.replicate r RB.Y ++ [RB.R1])
              = List.replicate (r + 1) RB.Y ++ [RB.R1] := by
            rw [List.replicate_succ, List.cons_append]
          rw [he]
          exact ih t (by simp at hlen; omega) hst' (hadm.suffix (List.suffix_cons _ _))
            (hg.suffix (List.suffix_cons _ _)) hv' (r + 1) (by omega)
      | .Z :: t =>
          have hst' : CStack t := by cases hst with | consZ h => exact h
          have hs1 : bstep b4 ⟨.Z :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
              = some (⟨t, .Lt, .X :: .P2 :: (List.replicate r .Y ++ [.R1])⟩, 4) := rfl
          refine Returns.of_run (BRun.of_step hs1) ?_
          exact returns_dP2 hst' (hadm.suffix (List.suffix_cons _ _))
            (hg.suffix (List.suffix_cons _ _)) (Or.inl rfl) (Or.inl (by omega))
      | .W :: t =>
          have hst' : CStack t := by cases hst with | consW h => exact h
          have hv' : 2 ≤ cval t := by simp only [cval_W] at hv; omega
          have hcrit : cval t = 2 → 4 ≤ bval t := by
            intro h2
            have hh := hg.head
            simp only [cval_W, bval_W, h2] at hh
            norm_num at hh
            omega
          have hcrit2 : cval t % 2 = 0 → (cval t : ℤ) + 2 ≤ bval t := by
            intro he
            have hh := hg.head
            simp only [cval_W, bval_W, if_neg (by omega : ¬ cval t % 2 = 1)] at hh
            have hdiv : ((cval t / 2 : ℕ) : ℤ) = (cval t : ℤ) / 2 := by omega
            rw [hdiv] at hh
            omega
          have hs1 : bstep b4 ⟨.W :: t, .Bt, List.replicate r .Y ++ [.R1]⟩
              = some (⟨t, .Lt, .F :: (List.replicate r .Y ++ [.R1])⟩, 2) := rfl
          refine Returns.of_run (BRun.of_step hs1) ?_
          exact hW t r hst' (hadm.suffix (List.suffix_cons _ _))
            (hg.suffix (List.suffix_cons _ _)) hv' hcrit hcrit2 hr
      | .J :: t => cases hst
      | .J1 :: t => cases hst
      | .J0 :: t => cases hst
      | .K0 :: t => cases hst
      | .K1 :: t => cases hst

/-- **The return theorem.** -/
theorem cp_returns (hW : WCase b4) {s : List LB} (h : SafeCP s) :
    ∃ (c₁ : BCfg) (k₁ : ℕ), 1 ≤ k₁ ∧ BRun b4 (cpCfg s) c₁ k₁ ∧ Returns b4 c₁ := by
  -- the checkpoint ends in a zero bit, which the sweep strips first
  obtain ⟨t, rfl⟩ := h.endX
  refine ⟨⟨t, .Bt, .Y :: (List.replicate 1 .Y ++ [.R1])⟩, 6, by omega,
    BRun.of_step rfl, ?_⟩
  have he2 : RB.Y :: (List.replicate 1 RB.Y ++ [RB.R1])
      = List.replicate 2 RB.Y ++ [RB.R1] := rfl
  rw [he2]
  have hst' : CStack t := by cases h.st with | consX hh => exact hh
  have hv' : 1 ≤ cval t := by have := h.pos; simp at this; omega
  exact returns_Bt_aux hW t.length t (le_refl _) hst'
    (h.adm.suffix (List.suffix_cons _ _)) (h.good.suffix (List.suffix_cons _ _)) hv' 2 (by omega)

/-! ## Non-halting -/

theorem halt_time_of_run {c c' : BCfg} {k n : ℕ} (hr : BRun b4 c c' k)
    (hn : steps (M b4) n c.den = none) : k < n ∧ steps (M b4) (n - k) c'.den = none := by
  have hlt : k < n := by
    by_contra hc
    exact not_halts_within hr.sound n (by omega) hn
  refine ⟨hlt, ?_⟩
  have : steps (M b4) (k + (n - k)) c.den = none := by
    rw [show k + (n - k) = n by omega]
    exact hn
  rw [steps_add, hr.sound] at this
  simpa using this

theorem not_halts_of_safeCP (hW : WCase b4) :
    ∀ (n : ℕ) (s : List LB), SafeCP s → steps (M b4) n (cpCfg s).den ≠ none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro s hs hn
      obtain ⟨c₁, k₁, hk₁, hrun₁, hret⟩ := cp_returns hW hs
      obtain ⟨hlt₁, hn₁⟩ := halt_time_of_run hrun₁ hn
      rcases hret with ⟨s', k', hs', hrun'⟩ | hnh
      · obtain ⟨hlt', hn'⟩ := halt_time_of_run hrun' hn₁
        exact ih (n - k₁ - k') (by omega) s' hs' hn'
      · exact hnh ⟨n - k₁, hn₁⟩

end BB25.Prefix
