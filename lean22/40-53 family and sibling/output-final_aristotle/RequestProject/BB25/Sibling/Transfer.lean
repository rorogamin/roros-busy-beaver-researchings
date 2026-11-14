/-
# Transferring block runs to the sibling machine

The sibling `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` differs from the family members
only in `B3` and `B4`.  A block step of the family simulator `bstep b4` reads
`B3` only in the pop rule `W <B1 → <A F`, and reads `B4` only at a `G = 241`
block, which is created from an `F = 141` block, which only the pop rule
creates.

We work with the block simulator at `b4 = none`, for which the `G` rule is
undefined.  Every *other* rule of `bstep none` except the pop rule is a valid
run of the sibling (`bstep_none_sound_sib`), even with arbitrary extra cells
below the left part of the tape as long as the rule does not look at the
bottom `^11` block.  The number of `F`/`G` blocks on the right never decreases
along a `bstep none` run and the pop rule increases it, so a run that starts
and ends without `F`/`G` blocks never pops, and is therefore a run of the
sibling (`BRun.sib`, `BRun.sib_frame`).

All the member-independent block runs of the project are proved for an
arbitrary `b4`, so they can be instantiated at `b4 = none` and transferred.
-/
import RequestProject.BB25.Sibling.Local

namespace BB25.Sibling

open BB25 BB25.Prefix

/-! ## Base configurations with extra cells at the bottom -/

/-- The base configuration of `c`, with the cells `b` added below the left
part of the tape. -/
def denB (c : BCfg) (b : List Sym) : Cfg := ⟨c.den.l ++ b, c.den.q, c.den.d, c.den.r⟩

theorem denB_nil (c : BCfg) : denB c [] = c.den := by
  obtain ⟨lt, st, rt⟩ := c
  cases st <;> simp [denB, BCfg.den]

/-! ## One block step -/

theorem bstep_none_fgc {c c' : BCfg} {k : ℕ} (h : bstep none c = some (c', k)) :
    fgc c.rt ≤ fgc c'.rt := by
  unfold bstep at h
  split at h <;>
    first
      | (rw [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         simp; try omega)
      | simp [gStep] at h

theorem bstep_none_noL {c c' : BCfg} {k : ℕ} (h : bstep none c = some (c', k))
    (hL : LB.L ∉ c.lt) : LB.L ∉ c'.lt := by
  unfold bstep at h
  split at h <;>
    first
      | (rw [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         simp_all)
      | simp [gStep] at h

/-- **Every rule of `bstep none` except the pop rule is a run of the sibling**,
also over extra bottom cells unless the rule reads the bottom `^11` block. -/
theorem bstep_none_sound_sib {c c' : BCfg} {k : ℕ} (h : bstep none c = some (c', k))
    (hW : ¬ ∃ rest rt, c = ⟨.W :: rest, .Bt, rt⟩) (b : List Sym)
    (hL : b = [] ∨ LB.L ∉ c.lt) :
    steps machine k (denB c b) = some (denB c' b) := by
  unfold bstep at h
  split at h
  all_goals
    first
      | (simp [gStep] at h; done)
      | exact absurd ⟨_, _, rfl⟩ hW
      | (rw [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         first
           | rfl
           | (rcases hL with rfl | hL
              · rfl
              · simp at hL))

/-! ## Block runs -/

theorem bsteps_none_fgc : ∀ (n : ℕ) (c c' : BCfg) (k : ℕ),
    bsteps none n c = some (c', k) → fgc c.rt ≤ fgc c'.rt := by
  intro n
  induction n with
  | zero =>
      intro c c' k h
      simp only [bsteps, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact le_refl _
  | succ n ih =>
      intro c c' k h
      rw [bsteps, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c₁, k₁⟩, hb, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨c₂, k₂⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact le_trans (bstep_none_fgc hb) (ih c₁ c₂ k₂ hr)

theorem bsteps_none_sib (b : List Sym) : ∀ (n : ℕ) (c c' : BCfg) (k : ℕ),
    bsteps none n c = some (c', k) → fgc c.rt = 0 → fgc c'.rt = 0 →
    (b = [] ∨ LB.L ∉ c.lt) → steps machine k (denB c b) = some (denB c' b) := by
  intro n
  induction n with
  | zero =>
      intro c c' k h _ _ _
      simp only [bsteps, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | succ n ih =>
      intro c c' k h h0 h1 hL
      rw [bsteps, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c₁, k₁⟩, hb, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨c₂, k₂⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hf1 : fgc c₁.rt = 0 := by
        have := bsteps_none_fgc n c₁ c₂ k₂ hr
        omega
      have hW : ¬ ∃ rest rt, c = ⟨.W :: rest, .Bt, rt⟩ := by
        rintro ⟨rest, rt, rfl⟩
        have hb' : bstep none ⟨.W :: rest, .Bt, rt⟩ = some (⟨rest, .Lt, .F :: rt⟩, 2) := rfl
        rw [hb'] at hb
        cases hb
        simp at hf1
      have hL1 : b = [] ∨ LB.L ∉ c₁.lt := by
        rcases hL with hL | hL
        · exact Or.inl hL
        · exact Or.inr (bstep_none_noL hb hL)
      exact steps_trans (bstep_none_sound_sib hb hW b hL) (ih c₁ c₂ k₂ hr hf1 h1 hL1)

/-- **A `bstep none` run without `F`/`G` blocks at its ends is a run of the
sibling.** -/
theorem _root_.BB25.BRun.sib {c c' : BCfg} {k : ℕ} (h : BRun none c c' k) (h0 : fgc c.rt = 0)
    (h1 : fgc c'.rt = 0) : steps machine k c.den = some c'.den := by
  obtain ⟨n, h⟩ := h
  have := bsteps_none_sib [] n c c' k h h0 h1 (Or.inl rfl)
  rwa [denB_nil, denB_nil] at this

/-- **The same, over arbitrary extra bottom cells**, for a run that never sees
the bottom block `^11`. -/
theorem _root_.BB25.BRun.sib_frame {c c' : BCfg} {k : ℕ} (h : BRun none c c' k) (h0 : fgc c.rt = 0)
    (h1 : fgc c'.rt = 0) (hL : LB.L ∉ c.lt) (b : List Sym) :
    steps machine k (denB c b) = some (denB c' b) := by
  obtain ⟨n, h⟩ := h
  exact bsteps_none_sib b n c c' k h h0 h1 (Or.inr hL)

end BB25.Sibling
