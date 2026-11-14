/-!
# The Turing machine `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB`

Two states `A`, `B`, five symbols `0 … 4`.

|   | 0   | 1   | 2   | 3   | 4   |
|---|-----|-----|-----|-----|-----|
| A | 1RB | 2LA | 0RB | --- | 4LA |
| B | 1LA | 3LA | 1RA | 4RA | 1LB |

A configuration stores the state, the cells to the left of the head (nearest
first) and the list consisting of the head cell followed by the cells to its
right.  Missing cells are blank (`0`).

This file contains the complete trusted statement: the machine, `Reaches`, `Halts`
and `init`.  Everything else in the project is proof.
-/

namespace TM25

inductive St | A | B deriving DecidableEq, Repr

abbrev Sym := Fin 5

/-- A machine configuration.  `l` = cells left of the head, nearest first;
`r` = head cell followed by the cells to its right.  Absent cells are `0`. -/
structure Cfg where
  st : St
  l : List Sym
  r : List Sym
deriving DecidableEq, Repr

/-- The transition table: `(written symbol, move right?, next state)`,
or `none` for the halting transition `A3`. -/
def delta : St → Sym → Option (Sym × Bool × St)
  | .A, 0 => some (1, true, .B)
  | .A, 1 => some (2, false, .A)
  | .A, 2 => some (0, true, .B)
  | .A, 3 => none
  | .A, 4 => some (4, false, .A)
  | .B, 0 => some (1, false, .A)
  | .B, 1 => some (3, false, .A)
  | .B, 2 => some (1, true, .A)
  | .B, 3 => some (4, true, .A)
  | .B, 4 => some (1, false, .B)

/-- One step of the machine (`none` = the machine halts). -/
def step (c : Cfg) : Option Cfg :=
  match delta c.st (c.r.headD 0) with
  | none => none
  | some (w, true, s) => some ⟨s, w :: c.l, c.r.tail⟩
  | some (w, false, s) => some ⟨s, c.l.tail, c.l.headD 0 :: w :: c.r.tail⟩

/-- `Reaches c c'`: the machine started in `c` reaches `c'` after finitely many steps
(reflexive-transitive closure of `step`). -/
inductive Reaches : Cfg → Cfg → Prop
  | refl (c : Cfg) : Reaches c c
  | head {a b c : Cfg} : step a = some b → Reaches b c → Reaches a c

/-- The machine started in `c` eventually halts. -/
def Halts (c : Cfg) : Prop :=
  ∃ c', Reaches c c' ∧ step c' = none

/-- The initial configuration: state `A` on an all-blank tape. -/
def init : Cfg := ⟨.A, [], []⟩

/-- `n` iterated steps (stays at `none` once halted). -/
def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

theorem Reaches.trans {a b c : Cfg} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  induction h1 with
  | refl => exact h2
  | head hs _ ih => exact Reaches.head hs (ih h2)

theorem Reaches.single {a b : Cfg} (h : step a = some b) : Reaches a b :=
  Reaches.head h (Reaches.refl b)

theorem Reaches.of_eq {a b : Cfg} (h : a = b) : Reaches a b := h ▸ Reaches.refl a

/-- The successor configuration (or the configuration itself if it is halting). -/
def next (c : Cfg) : Cfg := (step c).getD c

theorem Reaches.next_of {a c : Cfg} (hs : (step a).isSome) (h : Reaches (next a) c) :
    Reaches a c := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  exact Reaches.head hb (by simpa [next, hb] using h)

/-- Perform one (non-halting) step of the machine in a `Reaches` goal. -/
macro "tm_step" : tactic =>
  `(tactic| (refine Reaches.next_of (by simp [step, delta]) ?_; simp only [next, step, delta,
    List.headD_cons, List.tail_cons, List.headD_nil, List.tail_nil, Option.getD_some,
    List.cons_append, List.nil_append]))

/-! ### Basic sweeps -/

theorem replicate_two_mul_succ {α : Type} (k : Nat) (x : α) :
    List.replicate (2 * (k + 1)) x = x :: x :: List.replicate (2 * k) x := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]; rfl

theorem replicate_append_cons {α : Type} (n : Nat) (x : α) (L : List α) :
    List.replicate n x ++ x :: L = x :: (List.replicate n x ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- Rightward sweep: `B>` over `2^(2j)` writes `(10)^j`. -/
theorem sweep_right (j : Nat) (L R : List Sym) :
    Reaches ⟨.B, L, List.replicate (2 * j) 2 ++ R⟩
      ⟨.B, (List.replicate j [(0 : Sym), 1]).flatten ++ L, R⟩ := by
  induction j generalizing L with
  | zero => simpa using Reaches.refl _
  | succ j ih =>
    rw [replicate_two_mul_succ]
    refine Reaches.head (b := ⟨.A, 1 :: L, 2 :: (List.replicate (2 * j) 2 ++ R)⟩) ?_ ?_
    · simp [step, delta]
    refine Reaches.head (b := ⟨.B, 0 :: 1 :: L, List.replicate (2 * j) 2 ++ R⟩) ?_ ?_
    · simp [step, delta]
    refine (ih _).trans (Reaches.of_eq ?_)
    simp [List.replicate_succ']

/-- Leftward sweep: `<A` over `1^(n+1)` writes `2^(n+1)`. -/
theorem sweep_left_ones (n : Nat) (x : Sym) (L R : List Sym) :
    Reaches ⟨.A, List.replicate n 1 ++ x :: L, 1 :: R⟩
      ⟨.A, L, x :: List.replicate (n + 1) 2 ++ R⟩ := by
  induction n generalizing R with
  | zero => exact Reaches.single (by simp [step, delta])
  | succ n ih =>
    refine Reaches.head (b := ⟨.A, List.replicate n 1 ++ x :: L, 1 :: 2 :: R⟩) ?_ ?_
    · simp [step, delta, List.replicate_succ]
    refine (ih _).trans (Reaches.of_eq ?_)
    simp [List.replicate_succ']

end TM25
