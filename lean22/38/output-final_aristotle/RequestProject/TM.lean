/-
# The Turing machine `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`

A 2-state, 5-symbol Turing machine.  This file sets up the machine, a tape
representation, the step function, and the notion of (non)halting.

Transition table (state, read) ↦ (write, move, new state):

```
        0      1      2      3      4
  A    1RB    2LA    0RB    1LA    3LB
  B    1LA    3LB    1RA    4RA    ---
```

The only undefined entry is `(B, 4)`, so the machine halts exactly when it
reads a `4` in state `B`.
-/

namespace TM25

/-- The two states of the machine. -/
inductive St | A | B
  deriving DecidableEq, Repr

/-- A direction of motion / of reading. -/
inductive Dir | L | R
  deriving DecidableEq, Repr

open St Dir

/--
A configuration of the machine.

The tape is split into the cells strictly on one side of the head and the cells
on the other side, both stored nearest-cell-first, and extended by `0`s
(the blank symbol) beyond the ends of the two lists.

* If `d = Dir.L` the head sits on the cell `l.headD 0`, i.e. on the first cell
  of `l`, and `r` holds the cells strictly to its right.
* If `d = Dir.R` the head sits on the cell `r.headD 0`, i.e. on the first cell
  of `r`, and `l` holds the cells strictly to its left.

Both presentations of the same tape position are interchangeable: `⟨q, L, a::l, r⟩`
and `⟨q, R, l, a::r⟩` describe the same machine configuration and have the same
successor (see `step_shift`).
-/
structure Cfg where
  q : St
  d : Dir
  l : List Nat
  r : List Nat
  deriving DecidableEq, Repr

/-- The symbol currently under the head. -/
def Cfg.cur (c : Cfg) : Nat :=
  match c.d with
  | Dir.L => c.l.headD 0
  | Dir.R => c.r.headD 0

/-- The transition table.  `none` means the machine halts. -/
def trans : St → Nat → Option (Nat × Dir × St)
  | St.A, 0 => some (1, Dir.R, St.B)
  | St.A, 1 => some (2, Dir.L, St.A)
  | St.A, 2 => some (0, Dir.R, St.B)
  | St.A, 3 => some (1, Dir.L, St.A)
  | St.A, 4 => some (3, Dir.L, St.B)
  | St.B, 0 => some (1, Dir.L, St.A)
  | St.B, 1 => some (3, Dir.L, St.B)
  | St.B, 2 => some (1, Dir.R, St.A)
  | St.B, 3 => some (4, Dir.R, St.A)
  | _, _ => none

/-- One step of the machine; `none` if the machine halts. -/
def step (c : Cfg) : Option Cfg :=
  match trans c.q c.cur with
  | none => none
  | some (w, Dir.L, q') =>
    match c.d with
    | Dir.L => some ⟨q', Dir.L, c.l.tail, w :: c.r⟩
    | Dir.R => some ⟨q', Dir.L, c.l, w :: c.r.tail⟩
  | some (w, Dir.R, q') =>
    match c.d with
    | Dir.L => some ⟨q', Dir.R, w :: c.l.tail, c.r⟩
    | Dir.R => some ⟨q', Dir.R, w :: c.l, c.r.tail⟩

/-- `run n c` runs the machine for `n` steps from `c`, or returns `none` if it
halts before that. -/
def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

/-- The initial configuration: blank tape, state `A`. -/
def init : Cfg := ⟨St.A, Dir.R, [], []⟩

/-- The machine halts if it reaches a halting configuration after some number of
steps. -/
def Halts : Prop := ∃ n, run n init = none

@[simp] theorem run_zero (c : Cfg) : run 0 c = some c := rfl

theorem run_succ (n : Nat) (c : Cfg) : run (n + 1) c = (step c).bind (run n) := rfl

theorem run_bind (m n : Nat) (c : Cfg) :
    run (m + n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp
  | succ k ih =>
      have : k + 1 + n = (k + n) + 1 := by omega
      rw [this, run_succ, run_succ]
      cases step c with
      | none => simp
      | some c' => simpa using ih c'

/-- Chaining two computations. -/
theorem run_trans {m n : Nat} {a b c : Cfg} (h₁ : run m a = some b) (h₂ : run n b = some c) :
    run (m + n) a = some c := by
  rw [run_bind, h₁]; simpa using h₂


theorem run_isSome_of_le {m n : Nat} (hmn : m ≤ n) {c : Cfg} (h : (run n c).isSome) :
    (run m c).isSome := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [run_bind] at h
  cases hm : run m c with
  | none => rw [hm] at h; simp at h
  | some c' => simp

end TM25
