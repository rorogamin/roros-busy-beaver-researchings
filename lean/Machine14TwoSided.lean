/-
  Machine 14: a two-sided invariant for the 2025 block model.

  This is the block-level transcription of mxdys's tape language.  The left
  side has `L` as its far-end marker and only `U/W/F/Y/Q` before it; the right
  side has `R` as its far-end marker and only `V/C/C1/C2/P/X` before it.

  The predicate is deliberately structural.  It captures the two-sided shape
  of the reachable block words, but it does **not** exclude the block-level
  dead end `> R`: that state also satisfies the language.  The final theorem
  records this explicitly.
-/

import Machine14

namespace M14

/-- The left half of the two-sided language: a far-end `L`, with no other `L`
before it.  `cons` prepends a token nearer to the head. -/
inductive LeftOK : List LTok → Prop
  | nilL : LeftOK [LTok.L]
  | cons {x : LTok} {l : List LTok} (hx : x ≠ LTok.L) (hl : LeftOK l) :
      LeftOK (x :: l)

/-- The right half of the two-sided language: a far-end `R`, with no other `R`
before it.  `cons` prepends a token nearer to the head. -/
inductive RightOK : List RTok → Prop
  | nilR : RightOK [RTok.R]
  | cons {x : RTok} {r : List RTok} (hx : x ≠ RTok.R) (hr : RightOK r) :
      RightOK (x :: r)

/-- Base case for the left language. -/
@[simp] theorem LeftOK_nilL : LeftOK [LTok.L] := LeftOK.nilL

/-- Base case for the right language. -/
@[simp] theorem RightOK_nilR : RightOK [RTok.R] := RightOK.nilR

/-- The two concrete three-token left prefixes produced by `w> C` and `w> C1`. -/
@[simp] theorem LeftOK.QF_cons {x : LTok} {l : List LTok}
    (hx : x ≠ LTok.L) (hl : LeftOK l) :
    LeftOK (LTok.Q :: LTok.F :: x :: l) :=
  LeftOK.cons (by decide) (LeftOK.cons (by decide) (LeftOK.cons hx hl))

@[simp] theorem LeftOK.QU_cons {x : LTok} {l : List LTok}
    (hx : x ≠ LTok.L) (hl : LeftOK l) :
    LeftOK (LTok.Q :: LTok.U :: x :: l) :=
  LeftOK.cons (by decide) (LeftOK.cons (by decide) (LeftOK.cons hx hl))

/-- Introduction form used by `simp` to rebuild a left word after a rule. -/
@[simp] theorem LeftOK.cons_intro {x : LTok} {l : List LTok}
    (hx : x ≠ LTok.L) (hl : LeftOK l) : LeftOK (x :: l) :=
  LeftOK.cons hx hl

/-- Introduction form used by `simp` to rebuild a right word after a rule. -/
@[simp] theorem RightOK.cons_intro {x : RTok} {r : List RTok}
    (hx : x ≠ RTok.R) (hr : RightOK r) : RightOK (x :: r) :=
  RightOK.cons hx hr

/-- The two-sided block language. -/
def Inv2 (s : BState) : Prop :=
  LeftOK s.left ∧ RightOK s.right

/-- The block start lies in the language. -/
theorem initB_inv2 : Inv2 initB := by
  unfold Inv2
  refine ⟨?_, RightOK.nilR⟩
  exact LeftOK.cons (by decide)
    (LeftOK.cons (by decide) LeftOK.nilL)

/-- Every defined block rule preserves the two-sided language.  The `> R`
case is vacuous because `stepB` has no rule there; the theorem is about the
defined transitions only. -/
theorem stepB_inv2 {s s' : BState} (h : Inv2 s) (hs : stepB s = some s') :
    Inv2 s' := by
  rcases s with ⟨head, left, right⟩
  unfold Inv2 at h
  rcases h with ⟨hL, hR⟩
  cases hL <;> cases hR
  all_goals
    unfold stepB at hs
    split at hs <;>
      (first
       | (rw [Option.some.injEq] at hs
          subst s'
          unfold Inv2
          constructor <;> simp_all [LeftOK.QF_cons, LeftOK.QU_cons])
       | (simp at hs))

/-- Every left word in the language really contains the far-end `L`. -/
theorem LeftOK.mem_L {l : List LTok} (h : LeftOK l) : LTok.L ∈ l := by
  induction h with
  | nilL => simp
  | cons hx hl ih => simp [ih]

/-- Every right word in the language really contains the far-end `R`. -/
theorem RightOK.mem_R {r : List RTok} (h : RightOK r) : RTok.R ∈ r := by
  induction h with
  | nilR => simp
  | cons hx hr ih => simp [ih]

/-- The two-sided language is stronger than the old partition invariant. -/
theorem inv2_implies_inv {s : BState} (h : Inv2 s) : Inv s := by
  rcases h with ⟨hL, hR⟩
  exact ⟨LeftOK.mem_L hL, RightOK.mem_R hR⟩

/-- The invariant holds at every defined stage of the block run. -/
theorem runB_inv2 : ∀ n s, runB n = some s → Inv2 s
  | 0, s, hs => by
      simp [runB] at hs
      subst s
      exact initB_inv2
  | n + 1, s, hs => by
      simp [runB, ostepB] at hs
      cases h : runB n with
      | none => simp [h] at hs
      | some s0 =>
          simp [h] at hs
          exact stepB_inv2 (runB_inv2 n s0 h) hs

/-- The left/right language alone still contains the block-level dead end
`> R`.  Thus this invariant is a genuine structural invariant, not an
avoidance proof. -/
theorem inv2_contains_gtR : Inv2 ⟨Head.r, [LTok.L], [RTok.R]⟩ := by
  unfold Inv2
  exact ⟨LeftOK.nilL, RightOK.nilR⟩

/-- The language does not imply `AvoidsGtR`. -/
theorem inv2_not_avoids :
    ∃ s : BState, Inv2 s ∧ ¬ AvoidsGtR s := by
  refine ⟨⟨Head.r, [LTok.L], [RTok.R]⟩, inv2_contains_gtR, ?_⟩
  intro h
  exact h ⟨rfl, ⟨[], rfl⟩⟩

#print axioms M14.initB_inv2
#print axioms M14.stepB_inv2
#print axioms M14.inv2_implies_inv
#print axioms M14.runB_inv2
#print axioms M14.inv2_contains_gtR
#print axioms M14.inv2_not_avoids

end M14
