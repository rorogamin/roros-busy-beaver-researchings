import Mathlib

/-!
# The Turing machine `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---`

```
      0    1    2    3    4
  A  1RB  3LA  3LA  0RB  2LB
  B  2LA  4LA  4RA  2RA  ---
```

A configuration is `⟨left, st, right⟩`: `right` is the tape from the head cell
(inclusive) to the right, `left` the tape strictly left of the head, reversed.
Cells not covered by either list are `0`.
-/

namespace BB25

/-- The two states of the machine. -/
inductive St where
  | A : St
  | B : St

/-- Tape symbols `0,1,2,3,4`. -/
abbrev Sym := Fin 5

/-- Head movement. -/
inductive Dir where
  | L : Dir
  | R : Dir

/-- The transition table.  `none` is the halting transition, `B` reading `4`. -/
def tr : St → Sym → Option (Sym × Dir × St)
  | .A, 0 => some (1, .R, .B)
  | .A, 1 => some (3, .L, .A)
  | .A, 2 => some (3, .L, .A)
  | .A, 3 => some (0, .R, .B)
  | .A, 4 => some (2, .L, .B)
  | .B, 0 => some (2, .L, .A)
  | .B, 1 => some (4, .L, .A)
  | .B, 2 => some (4, .R, .A)
  | .B, 3 => some (2, .R, .A)
  | .B, 4 => none

/-- A configuration: reversed left half-tape, state, right half-tape (head on
the first cell of `right`). -/
structure Cfg where
  left : List Sym
  st : St
  right : List Sym

/-- One step of the machine; `none` if the machine halts. -/
def step (c : Cfg) : Option Cfg :=
  match tr c.st (c.right.headD 0) with
  | none => none
  | some (w, .R, s) => some ⟨w :: c.left, s, c.right.tail⟩
  | some (w, .L, s) => some ⟨c.left.tail, s, (c.left.headD 0) :: w :: c.right.tail⟩

/-- `n` steps of the machine. -/
def steps : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (steps n)

/-- The initial configuration: blank tape, state `A`. -/
def init : Cfg := ⟨[], .A, []⟩

/-- The machine halts (from the blank tape). -/
def Halts : Prop := ∃ n, steps n init = none

/-- Running `m` then `n` steps is running `m + n` steps. -/
theorem steps_add (m n : ℕ) (c : Cfg) :
    steps (m + n) c = (steps m c).bind (steps n) := by
  induction m generalizing c with
  | zero => simp [steps]
  | succ m ih =>
      cases h : step c with
      | none => simp [steps, Nat.succ_add, h]
      | some c' => simp [steps, Nat.succ_add, h, ih]

theorem steps_trans {m n : ℕ} {c c' c'' : Cfg}
    (h₁ : steps m c = some c') (h₂ : steps n c' = some c'') :
    steps (m + n) c = some c'' := by
  rw [steps_add, h₁]; simpa using h₂

end BB25
