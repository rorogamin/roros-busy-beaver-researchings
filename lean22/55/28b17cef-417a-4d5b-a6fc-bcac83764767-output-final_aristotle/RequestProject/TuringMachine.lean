/-
# The Turing machine `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---`

Basic definitions: the transition table, configurations, and the step relation.
-/
import Mathlib

namespace ShiftOverflow

/-- The two states of the machine. -/
inductive St where
  | A : St
  | B : St
deriving DecidableEq, Repr

/-- The transition table of `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---`.

Tape symbols are natural numbers; only `0,1,2,3,4` occur, `0` being the blank.
`tr s a = some (w, d, s')` means: in state `s` reading `a`, write `w`, move right
if `d = true` and left if `d = false`, and go to state `s'`.
`tr .B 4 = none` is the single halting instruction. -/
def tr : St → ℕ → Option (ℕ × Bool × St)
  | .A, 0 => some (1, true,  .B)   -- 1RB
  | .A, 1 => some (2, false, .A)   -- 2LA
  | .A, 2 => some (0, true,  .B)   -- 0RB
  | .A, 3 => some (4, false, .B)   -- 4LB
  | .A, 4 => some (0, false, .A)   -- 0LA
  | .B, 0 => some (1, false, .A)   -- 1LA
  | .B, 1 => some (3, false, .A)   -- 3LA
  | .B, 2 => some (1, true,  .A)   -- 1RA
  | .B, 3 => some (4, true,  .A)   -- 4RA
  | .B, 4 => none                  -- ---
  | _, _  => none

/-- A configuration: a bi-infinite tape, the head position, and the state. -/
structure Cfg where
  tape : ℤ → ℕ
  pos : ℤ
  st : St

/-- One step of the machine; `none` means the machine has halted. -/
def step (c : Cfg) : Option Cfg :=
  match tr c.st (c.tape c.pos) with
  | none => none
  | some (w, d, s) =>
      some ⟨Function.update c.tape c.pos w, (if d then c.pos + 1 else c.pos - 1), s⟩

/-- `n` steps of the machine. -/
def steps : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (steps n)

/-- Overwrite one tape cell. -/
def upd1 (t : ℤ → ℕ) (p : ℤ) (a : ℕ) : ℤ → ℕ := Function.update t p a

/-- Overwrite two consecutive tape cells. -/
def upd2 (t : ℤ → ℕ) (p : ℤ) (a b : ℕ) : ℤ → ℕ :=
  Function.update (Function.update t p a) (p + 1) b

/-- Overwrite three consecutive tape cells. -/
def upd3 (t : ℤ → ℕ) (p : ℤ) (a b c : ℕ) : ℤ → ℕ :=
  Function.update (Function.update (Function.update t p a) (p + 1) b) (p + 2) c

/-! ## The transition table, spelled out

These ten equations are exactly the ten instructions of the standard-format
description `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---`. -/

theorem tr_A0 : tr .A 0 = some (1, true, .B) := rfl
theorem tr_A1 : tr .A 1 = some (2, false, .A) := rfl
theorem tr_A2 : tr .A 2 = some (0, true, .B) := rfl
theorem tr_A3 : tr .A 3 = some (4, false, .B) := rfl
theorem tr_A4 : tr .A 4 = some (0, false, .A) := rfl
theorem tr_B0 : tr .B 0 = some (1, false, .A) := rfl
theorem tr_B1 : tr .B 1 = some (3, false, .A) := rfl
theorem tr_B2 : tr .B 2 = some (1, true, .A) := rfl
theorem tr_B3 : tr .B 3 = some (4, true, .A) := rfl
theorem tr_B4 : tr .B 4 = none := rfl

end ShiftOverflow
