/-
  Machine 14: the clean left counter and the right X-buffer.

  The actual block run uses `Q` and `Y` as transient left tokens.  Deleting
  them from the left stack leaves a word over `U`, `W`, `F` resting on `L`.
  This file formalizes that clean language and the mixed-radix counter value
  used by the related 13-machine family:

    cval [L]       = 0
    cval (U :: s)  = 2 * cval s + 1
    cval (W :: s)  = 2 * cval s
    cval (F :: s)  = cval s / 2

  It also defines `xcount`, the number of `X` tokens on the right.  The final
  theorems record that the obvious relations between `cval` and `xcount` fail
  on the actual block run.  This is a search/formalization layer, not a
  totality or nonhalting proof.
-/

import Machine14

namespace M14

/-- The clean left language: a word of `U`, `W`, `F` tokens resting on the
far-end `L`, stored nearest-to-head first. -/
inductive CleanL : List LTok → Prop
  | base : CleanL [LTok.L]
  | u {l : List LTok} : CleanL l → CleanL (LTok.U :: l)
  | w {l : List LTok} : CleanL l → CleanL (LTok.W :: l)
  | f {l : List LTok} : CleanL l → CleanL (LTok.F :: l)

/-- Delete the transient `Q` and `Y` tokens from a left stack. -/
def stripQY : List LTok → List LTok
  | [] => []
  | x :: xs =>
      if x = LTok.Q ∨ x = LTok.Y then stripQY xs
      else x :: stripQY xs

/-- Mixed-radix counter value of a clean left stack.  On non-clean inputs the
transient `Q` and `Y` are ignored, which is the natural extension used by the
search. -/
def cval : List LTok → Nat
  | [] => 0
  | LTok.L :: _ => 0
  | LTok.U :: xs => 2 * cval xs + 1
  | LTok.W :: xs => 2 * cval xs
  | LTok.F :: xs => cval xs / 2
  | LTok.Y :: xs => cval xs
  | LTok.Q :: xs => cval xs

/-- Number of `X` tokens on the right. -/
def xcount : List RTok → Nat
  | [] => 0
  | RTok.X :: xs => xcount xs + 1
  | _ :: xs => xcount xs

/-- The clean counter value of a block state. -/
def cvalB (s : BState) : Nat := cval (stripQY s.left)

/-- The right `X`-buffer size of a block state. -/
def xcountB (s : BState) : Nat := xcount s.right

@[simp] theorem cval_L : cval [LTok.L] = 0 := rfl

@[simp] theorem cval_U (s : List LTok) : cval (LTok.U :: s) = 2 * cval s + 1 := rfl

@[simp] theorem cval_W (s : List LTok) : cval (LTok.W :: s) = 2 * cval s := rfl

@[simp] theorem cval_F (s : List LTok) : cval (LTok.F :: s) = cval s / 2 := rfl

@[simp] theorem xcount_nil : xcount [] = 0 := rfl

@[simp] theorem xcount_X (s : List RTok) : xcount (RTok.X :: s) = xcount s + 1 := rfl

/-- The initial left stack, after deleting its transient `Q`, is clean. -/
theorem clean_init_core : CleanL (stripQY initB.left) := by
  simp [stripQY, initB]
  exact CleanL.u CleanL.base

/-- The initial counter value is one. -/
theorem cvalB_init : cvalB initB = 1 := by
  decide

/-- The initial right stack has no `X`. -/
theorem xcountB_init : xcountB initB = 0 := by
  decide

/-- The block state after four block steps. -/
def s4 : BState :=
  ⟨Head.l, [LTok.W, LTok.L], [RTok.X, RTok.R]⟩

/-- Four actual block steps reach `s4`. -/
theorem runB_four : runB 4 = some s4 := by
  decide

/-- At `s4` the clean counter is zero. -/
theorem cvalB_s4 : cvalB s4 = 0 := by
  decide

/-- At `s4` the right X-buffer has size one. -/
theorem xcountB_s4 : xcountB s4 = 1 := by
  decide

/-- The clean core remains clean at `s4`. -/
theorem clean_s4_core : CleanL (stripQY s4.left) := by
  simp [stripQY, s4]
  exact CleanL.w CleanL.base

/-- `cval >= xcount` is not a reachable invariant. -/
theorem cval_ge_xcount_fails :
    ∃ n s, runB n = some s ∧ cvalB s < xcountB s := by
  refine ⟨4, s4, runB_four, ?_⟩
  decide

/-- Even the weaker implication `cval = 0 -> xcount = 0` fails. -/
theorem zero_cval_zero_x_fails :
    ∃ n s, runB n = some s ∧ cvalB s = 0 ∧ xcountB s ≠ 0 := by
  refine ⟨4, s4, runB_four, ?_, ?_⟩
  · exact cvalB_s4
  · rw [xcountB_s4]
    decide

/-- The parity relation `(cval + xcount) % 2 = 0` fails at the start. -/
theorem parity_fails :
    ∃ n s, runB n = some s ∧ (cvalB s + xcountB s) % 2 ≠ 0 := by
  refine ⟨0, initB, rfl, ?_⟩
  decide

/-- There is no simple monotone lower bound `cval >= k * xcount` with `k >= 1`
at `s4`, because `cval = 0` and `xcount = 1`. -/
theorem cval_ge_two_x_fails :
    ∃ n s, runB n = some s ∧ cvalB s < 2 * xcountB s := by
  refine ⟨4, s4, runB_four, ?_⟩
  decide

#print axioms M14.clean_init_core
#print axioms M14.cvalB_init
#print axioms M14.xcountB_init
#print axioms M14.runB_four
#print axioms M14.cval_ge_xcount_fails
#print axioms M14.zero_cval_zero_x_fails
#print axioms M14.parity_fails
#print axioms M14.cval_ge_two_x_fails

end M14
