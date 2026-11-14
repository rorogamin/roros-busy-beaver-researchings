/-
# Local transit lemmas

Each lemma below describes one uninterrupted passage of the head through a short
window of the tape, starting either at the left end of the window moving right
(`transitL_…`) or at the right end of the window moving left (`transitR_…`).
Outside the window the tape is an arbitrary function `t : ℤ → ℕ`, so these are
genuinely context-free facts: while the head is inside the window, the rest of
the tape is irrelevant.

The head always enters in state `A`; this is consistent, because every transit
below also *leaves* its window in state `A`.

`transitL_xy` : the window is the pair of cells `p, p+1`, holding `x` then `y`,
and the head starts on cell `p`.
`transitR_xy` : same window, but the head starts on cell `p+1` (it is moving
leftwards, coming from the token to the right).
-/
import RequestProject.TuringMachine

namespace ShiftOverflow

local macro "finish_transit" : tactic =>
  `(tactic| (try refine ⟨?_, ?_⟩
             all_goals first
               | rfl
               | omega
               | (funext i; simp only [Function.update_apply]; split_ifs <;> omega)))

/-! ## Entering a two-cell window from the left, in state `A` -/

/-- `A> 2 2` : the head crosses the window, leaving `0 1`. -/
theorem transitL_22 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 2) :
    steps 2 ⟨t, p, .A⟩ = some ⟨upd2 t p 0 1, p + 2, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 2 1` : the head crosses the window, leaving `1 4`. -/
theorem transitL_21 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 1) :
    steps 4 ⟨t, p, .A⟩ = some ⟨upd2 t p 1 4, p + 2, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 2 0` : the head turns around inside the window and leaves to the left,
leaving `2 3`. -/
theorem transitL_20 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 0) :
    steps 5 ⟨t, p, .A⟩ = some ⟨upd2 t p 2 3, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 2 3` : the head crosses the window, leaving `0 4`. -/
theorem transitL_23 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 3) :
    steps 2 ⟨t, p, .A⟩ = some ⟨upd2 t p 0 4, p + 2, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 0 2` : the head crosses the window, leaving `1 1`. -/
theorem transitL_02 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 0) (h1 : t (p + 1) = 2) :
    steps 2 ⟨t, p, .A⟩ = some ⟨upd2 t p 1 1, p + 2, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 0 0` : the head turns around and leaves to the left, leaving `2 1`. -/
theorem transitL_00 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 0) (h1 : t (p + 1) = 0) :
    steps 3 ⟨t, p, .A⟩ = some ⟨upd2 t p 2 1, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `A> 1` : a lone cell holding `1` turns the head around; the cell becomes `2`. -/
theorem transitL_1 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 1) :
    steps 1 ⟨t, p, .A⟩ = some ⟨upd1 t p 2, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, upd1]

/-- `A> 4` : a lone cell holding `4` turns the head around; the cell becomes `0`. -/
theorem transitL_4 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 4) :
    steps 1 ⟨t, p, .A⟩ = some ⟨upd1 t p 0, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, upd1]

/-- `A> 2 2 3` : the head bounces about inside this three-cell window and finally
leaves it to the left, leaving `2 0 0`. -/
theorem transitL_223 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 2)
    (h2 : t (p + 2) = 3) :
    steps 9 ⟨t, p, .A⟩ = some ⟨upd3 t p 2 0 0, p - 1, .A⟩ := by
  have e1 : p + 1 + 1 = p + 2 := by ring
  have e2 : p + 2 - 1 = p + 1 := by ring
  have e3 : p + 1 - 1 = p := by ring
  simp [steps, step, tr, h0, h1, h2, upd3, e1, e2, e3]
  finish_transit

/-- `A> 0 2 3` : the head leaves this three-cell window to the left, leaving `2 3 4`. -/
theorem transitL_023 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 0) (h1 : t (p + 1) = 2)
    (h2 : t (p + 2) = 3) :
    steps 5 ⟨t, p, .A⟩ = some ⟨upd3 t p 2 3 4, p - 1, .A⟩ := by
  have e1 : p + 1 + 1 = p + 2 := by ring
  have e2 : p + 2 - 1 = p + 1 := by ring
  have e3 : p + 1 - 1 = p := by ring
  simp [steps, step, tr, h0, h1, h2, upd3, e1, e2, e3]
  finish_transit

/-! ## Entering a two-cell window from the right, in state `A` -/

/-- `0 1 <A` : the head bounces back to the right, leaving `1 1`. -/
theorem transitR_01 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 0) (h1 : t (p + 1) = 1) :
    steps 3 ⟨t, p + 1, .A⟩ = some ⟨upd2 t p 1 1, p + 2, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `1 1 <A` : the head passes on to the left, leaving `2 2`. -/
theorem transitR_11 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 1) (h1 : t (p + 1) = 1) :
    steps 2 ⟨t, p + 1, .A⟩ = some ⟨upd2 t p 2 2, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `1 4 <A` : the head passes on to the left, leaving `2 0`. -/
theorem transitR_14 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 1) (h1 : t (p + 1) = 4) :
    steps 2 ⟨t, p + 1, .A⟩ = some ⟨upd2 t p 2 0, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

/-- `0 4 <A` : the head passes on to the left, leaving `2 1`. -/
theorem transitR_04 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 0) (h1 : t (p + 1) = 4) :
    steps 4 ⟨t, p + 1, .A⟩ = some ⟨upd2 t p 2 1, p - 1, .A⟩ := by
  simp [steps, step, tr, h0, h1, upd2]
  finish_transit

end ShiftOverflow
