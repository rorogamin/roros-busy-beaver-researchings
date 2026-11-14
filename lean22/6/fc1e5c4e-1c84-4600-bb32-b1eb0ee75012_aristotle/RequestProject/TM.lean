module

/-
# The Turing machine `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---`

A 2-state, 5-symbol Turing machine.  State `A` on symbols `0,1,2,3,4` does
`1RB, 4RA, 1LA, 4RB, 2LA`; state `B` does `2LB, 3LA, 1RB, 2RA, HALT`
(the only halting transition is `B` reading the symbol `4`).

This file contains the basic definitions: symbols, states, configurations
(as a zipper over the bi-infinite tape, whose cells outside the two finite
lists are blank, i.e. `0`), the step function, the iterated step function
`run`, the initial configuration and the halting predicate.
-/

@[expose] public section

namespace BCM

/-- The two states of the machine. -/
inductive St
  | A
  | B
deriving DecidableEq, Repr

/-- Tape symbols: `0` is the blank. -/
abbrev Sym := Fin 5

/-- A configuration: the current state, the tape to the left of the head
(nearest cell first), the symbol under the head, and the tape to the right of
the head (nearest cell first).  All cells not listed are blank. -/
structure Cfg where
  st : St
  left : List Sym
  cur : Sym
  right : List Sym
deriving DecidableEq, Repr

/-- Head of a list, `0` (blank) for the empty list. -/
def hdz : List Sym → Sym
  | [] => 0
  | a :: _ => a

/-- Tail of a list, `[]` for the empty list. -/
def tlz : List Sym → List Sym
  | [] => []
  | _ :: t => t

/-- Write `w`, move left, go to state `s`. -/
def mvL (w : Sym) (s : St) (c : Cfg) : Cfg := ⟨s, tlz c.left, hdz c.left, w :: c.right⟩

/-- Write `w`, move right, go to state `s`. -/
def mvR (w : Sym) (s : St) (c : Cfg) : Cfg := ⟨s, w :: c.left, hdz c.right, tlz c.right⟩

/-- One step of the machine; `none` means the machine has halted. -/
def step (c : Cfg) : Option Cfg :=
  match c.st, c.cur with
  | .A, 0 => some (mvR 1 .B c)
  | .A, 1 => some (mvR 4 .A c)
  | .A, 2 => some (mvL 1 .A c)
  | .A, 3 => some (mvR 4 .B c)
  | .A, 4 => some (mvL 2 .A c)
  | .B, 0 => some (mvL 2 .B c)
  | .B, 1 => some (mvL 3 .A c)
  | .B, 2 => some (mvR 1 .B c)
  | .B, 3 => some (mvR 2 .A c)
  | .B, 4 => none

/-- `n` steps of the machine; `none` if the machine halts within those steps. -/
def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

/-- The initial configuration: state `A` on an all-blank tape. -/
def init : Cfg := ⟨.A, [], 0, []⟩

/-- The machine halts if some finite run from the initial configuration dies. -/
def Halts : Prop := ∃ n, run n init = none

theorem run_zero (c : Cfg) : run 0 c = some c := rfl

theorem run_succ (n : Nat) (c : Cfg) : run (n + 1) c = (step c).bind (run n) := rfl

/-- Composing two runs. -/
theorem run_comp {a b : Nat} {c d e : Cfg}
    (h1 : run a c = some d) (h2 : run b d = some e) : run (a + b) c = some e := by
  induction a generalizing c with
  | zero =>
      have : c = d := by
        have := h1
        simp [run] at this
        exact this
      subst this
      simpa using h2
  | succ n ih =>
      rw [show n + 1 + b = (n + b) + 1 from by omega, run_succ]
      rw [run_succ] at h1
      cases hs : step c with
      | none => rw [hs] at h1; simp at h1
      | some c' =>
          rw [hs] at h1
          simp only [Option.bind] at h1 ⊢
          exact ih h1

/-- If a run of `a + b` steps succeeds, so does the run of its first `a` steps. -/
theorem run_ne_none_of_le {a b : Nat} {c d : Cfg} (h : run (a + b) c = some d) :
    run a c ≠ none := by
  induction a generalizing c with
  | zero => simp [run]
  | succ n ih =>
      rw [show n + 1 + b = (n + b) + 1 from by omega, run_succ] at h
      rw [run_succ]
      cases hs : step c with
      | none => rw [hs] at h; simp at h
      | some c' =>
          rw [hs] at h
          simp only [Option.bind] at h ⊢
          exact ih h

end BCM
