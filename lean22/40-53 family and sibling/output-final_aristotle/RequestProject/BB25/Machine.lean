/-
# The BB(2,5) family `1RB2LA0RB1LB---_1LA3RA1RA4LB---`

This file sets up the basic machinery: symbols, states, directed-head
configurations, the step function, and the 13 members of the family.

The family consists of the 2-state 5-symbol Turing machines

```
  A0 = 1RB   A1 = 2LA   A2 = 0RB   A3 = 1LB   A4 = ---
  B0 = 1LA   B1 = 3RA   B2 = 1RA   B3 = 4LB   B4 = ?
```

where `B4` is the only free transition.  The only halting transition is `A4`,
so the machine halts exactly when it reads the symbol `4` in state `A`.
-/
import Mathlib

namespace BB25

/-! ## Configurations -/

/-- Direction of a move / of the head. -/
inductive Dir | L | R
deriving DecidableEq, Repr, Inhabited

/-- Tape symbols `0,1,2,3,4`. -/
abbrev Sym := Fin 5

/-- The two states. -/
inductive St | A | B
deriving DecidableEq, Repr, Inhabited

/-- A transition table: on a state and the symbol under the head, either the
machine halts (`none`) or it writes a symbol, moves, and changes state. -/
abbrev Machine := St → Sym → Option (Sym × Dir × St)

/--
A configuration in *directed head* notation.

`⟨l, q, d, r⟩` denotes the tape `… l.reverse ‖ r …` (all cells outside the two
lists carrying the symbol `0`), where `‖` is the position of the *marker*: `l`
lists the cells to the left of the marker, nearest cell first, `r` lists the
cells to its right, nearest cell first.  The head sits on the cell adjacent to
the marker in direction `d`, in state `q`.

So `⟨l, .A, .L, r⟩` is written `l.reverse <A r` and `⟨l, .A, .R, r⟩` is written
`l.reverse A> r` in the usual bbchallenge notation.
-/
structure Cfg where
  l : List Sym
  q : St
  d : Dir
  r : List Sym
deriving DecidableEq, Repr

/-- The symbol currently under the head. -/
def Cfg.read (c : Cfg) : Sym :=
  match c.d with
  | .L => c.l.headD 0
  | .R => c.r.headD 0

/-- One step of the machine; `none` means the machine halted. -/
def step (m : Machine) (c : Cfg) : Option Cfg :=
  match c with
  | ⟨l, q, .L, r⟩ =>
    match m q (l.headD 0) with
    | none => none
    | some (w, .L, q') => some ⟨l.tail, q', .L, w :: r⟩
    | some (w, .R, q') => some ⟨w :: l.tail, q', .R, r⟩
  | ⟨l, q, .R, r⟩ =>
    match m q (r.headD 0) with
    | none => none
    | some (w, .L, q') => some ⟨l, q', .L, w :: r.tail⟩
    | some (w, .R, q') => some ⟨w :: l, q', .R, r.tail⟩

/-- `n` steps of the machine. -/
def steps (m : Machine) : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step m c).bind (steps m n)

@[simp] theorem steps_zero (m : Machine) (c : Cfg) : steps m 0 c = some c := rfl

theorem steps_succ (m : Machine) (n : ℕ) (c : Cfg) :
    steps m (n + 1) c = (step m c).bind (steps m n) := rfl

theorem steps_add (m : Machine) (a b : ℕ) (c : Cfg) :
    steps m (a + b) c = (steps m a c).bind (steps m b) := by
  induction a generalizing c with
  | zero => simp [steps]
  | succ a ih =>
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h, steps_succ, steps_succ]
      cases step m c with
      | none => simp
      | some c' => simpa using ih c'

/-- Composing two runs. -/
theorem steps_trans {m : Machine} {a b : ℕ} {c c' c'' : Cfg}
    (h1 : steps m a c = some c') (h2 : steps m b c' = some c'') :
    steps m (a + b) c = some c'' := by
  rw [steps_add, h1]; simpa using h2

/-- The machine halts, started from `c`. -/
def Halts (m : Machine) (c : Cfg) : Prop := ∃ n, steps m n c = none

/-- A completed run of length `k` witnesses that the machine has not halted
within `k` steps. -/
theorem not_halts_within {m : Machine} {k : ℕ} {c c' : Cfg}
    (h : steps m k c = some c') (n : ℕ) (hn : n ≤ k) : steps m n c ≠ none := by
  intro hnone
  obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
  rw [steps_add, hnone] at h
  simp at h

/-! ## The family -/

/-- The state-`A` transitions, shared by all members of the family. -/
def famA : Sym → Option (Sym × Dir × St)
  | 0 => some (1, .R, .B)
  | 1 => some (2, .L, .A)
  | 2 => some (0, .R, .B)
  | 3 => some (1, .L, .B)
  | 4 => none

/-- The state-`B` transitions; `b4` is the free transition of the family. -/
def famB (b4 : Option (Sym × Dir × St)) : Sym → Option (Sym × Dir × St)
  | 0 => some (1, .L, .A)
  | 1 => some (3, .R, .A)
  | 2 => some (1, .R, .A)
  | 3 => some (4, .L, .B)
  | 4 => b4

/-- The member of the family with transition `b4` for `B4`. -/
def M (b4 : Option (Sym × Dir × St)) : Machine
  | .A => famA
  | .B => famB b4

/-! The 13 members listed on the bbchallenge wiki, named after their `B4`
transition. -/

def b4_2LB : Option (Sym × Dir × St) := some (2, .L, .B)
def b4_2RB : Option (Sym × Dir × St) := some (2, .R, .B)
def b4_1LB : Option (Sym × Dir × St) := some (1, .L, .B)
def b4_1RB : Option (Sym × Dir × St) := some (1, .R, .B)
def b4_0LB : Option (Sym × Dir × St) := some (0, .L, .B)
def b4_0RB : Option (Sym × Dir × St) := some (0, .R, .B)
def b4_3RA : Option (Sym × Dir × St) := some (3, .R, .A)
def b4_2LA : Option (Sym × Dir × St) := some (2, .L, .A)
def b4_2RA : Option (Sym × Dir × St) := some (2, .R, .A)
def b4_1LA : Option (Sym × Dir × St) := some (1, .L, .A)
def b4_1RA : Option (Sym × Dir × St) := some (1, .R, .A)
def b4_0LA : Option (Sym × Dir × St) := some (0, .L, .A)
def b4_0RA : Option (Sym × Dir × St) := some (0, .R, .A)

/-- The all-`0` tape with the head in state `A`, facing right. -/
def init : Cfg := ⟨[], .A, .R, []⟩

end BB25
