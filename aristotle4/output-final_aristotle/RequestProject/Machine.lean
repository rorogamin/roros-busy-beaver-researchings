import Mathlib

/-
# The 2-state, 5-symbol Turing machine `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`

This file contains a self-contained formalisation of the Turing machine

```
      0     1     2     3     4
  A  1RB   ---   3RA   2LA   2RB
  B  2LB   3LA   4LB   4RA   0RA
```

started on the all-`0` tape in state `A`, together with the facts about its
halting behaviour that we were able to establish rigorously.

The single undefined transition is `A` reading `1`; consequently the machine
halts if and only if it ever reads the symbol `1` while in state `A`
(`halts_iff_state_A_reads_one`).

The two "local" lemmas `halt_trap` and `no_halt_escape` isolate the exact
micro-pattern that decides the fate of the machine; see `ANALYSIS.md` for the
dynamical analysis explaining why these two patterns are the only relevant
ones.
-/

namespace TM2x5

/-- The two states of the machine. -/
inductive St
  | A
  | B
  deriving DecidableEq, Repr

/-- The five tape symbols; `s0` is the blank. -/
inductive Sym
  | s0
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr

instance : OfNat Sym 0 := ⟨Sym.s0⟩
instance : OfNat Sym 1 := ⟨Sym.s1⟩
instance : OfNat Sym 2 := ⟨Sym.s2⟩
instance : OfNat Sym 3 := ⟨Sym.s3⟩
instance : OfNat Sym 4 := ⟨Sym.s4⟩

/-- A configuration: the state, the tape to the left of the head (nearest cell
first), the symbol under the head, and the tape to its right (nearest cell
first).  Cells outside the two lists are blank (`0`). -/
structure Cfg where
  st : St
  left : List Sym
  cur : Sym
  right : List Sym
  deriving DecidableEq, Repr

namespace Cfg

/-- Write `w` in the current cell, move one cell to the left, enter state `s`. -/
def wL (c : Cfg) (w : Sym) (s : St) : Cfg :=
  match c.left with
  | [] => ⟨s, [], 0, w :: c.right⟩
  | x :: xs => ⟨s, xs, x, w :: c.right⟩

/-- Write `w` in the current cell, move one cell to the right, enter state `s`. -/
def wR (c : Cfg) (w : Sym) (s : St) : Cfg :=
  match c.right with
  | [] => ⟨s, w :: c.left, 0, []⟩
  | x :: xs => ⟨s, w :: c.left, x, xs⟩

end Cfg

/-- One step of the machine; `none` means that the machine halts. -/
def step (c : Cfg) : Option Cfg :=
  match c.st, c.cur with
  | St.A, Sym.s0 => some (c.wR 1 St.B)
  | St.A, Sym.s1 => none
  | St.A, Sym.s2 => some (c.wR 3 St.A)
  | St.A, Sym.s3 => some (c.wL 2 St.A)
  | St.A, Sym.s4 => some (c.wR 2 St.B)
  | St.B, Sym.s0 => some (c.wL 2 St.B)
  | St.B, Sym.s1 => some (c.wL 3 St.A)
  | St.B, Sym.s2 => some (c.wL 4 St.B)
  | St.B, Sym.s3 => some (c.wR 4 St.A)
  | St.B, Sym.s4 => some (c.wR 0 St.A)

/-- One step, lifted to `Option Cfg` (a halted machine stays halted). -/
def ostep (o : Option Cfg) : Option Cfg := o.bind step

/-- `iter n` applies `ostep` `n` times (tail recursively, so that it can be
evaluated on large inputs). -/
def iter : ℕ → Option Cfg → Option Cfg
  | 0, o => o
  | n + 1, o => iter n (ostep o)

/-- The initial configuration: state `A` on the all-blank tape. -/
def init : Cfg := ⟨St.A, [], 0, []⟩

/-- The configuration after `n` steps (`none` if the machine halted earlier). -/
def run (n : ℕ) : Option Cfg := iter n (some init)

/-- The machine halts. -/
def Halts : Prop := ∃ n : ℕ, run n = none

/-! ## Elementary properties -/

@[simp] theorem ostep_none : ostep none = none := rfl

theorem step_eq_none_iff (c : Cfg) : step c = none ↔ (c.st = St.A ∧ c.cur = 1) := by
  obtain ⟨s, l, x, r⟩ := c
  cases s <;> cases x <;> simp [step, OfNat.ofNat]

/-- The machine can only halt in state `A`. -/
theorem no_halt_in_B (c : Cfg) (h : c.st = St.B) : step c ≠ none := by
  simp [step_eq_none_iff, h]

theorem iter_succ (n : ℕ) (o : Option Cfg) : iter (n + 1) o = ostep (iter n o) := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih => simpa [iter] using ih (ostep o)

@[simp] theorem run_zero : run 0 = some init := rfl

theorem run_succ (n : ℕ) : run (n + 1) = ostep (run n) := iter_succ n _

/-- Once halted, always halted. -/
theorem run_eq_none_of_le {m n : ℕ} (hmn : m ≤ n) (h : run m = none) : run n = none := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.le_zero.mp hmn
    rw [hm] at h
    exact h
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · have hle : m ≤ n := Nat.lt_succ_iff.mp h'
      simp [run_succ, ih hle]
    · have : m = n + 1 := Nat.le_antisymm hmn h'
      simpa [this] using h

/-- **Halting criterion.**  The machine halts if and only if at some time it is
in state `A` scanning the symbol `1`; this is simply because `A`/`1` is the only
undefined entry of the transition table. -/
theorem halts_iff_state_A_reads_one :
    Halts ↔ ∃ (n : ℕ) (c : Cfg), run n = some c ∧ c.st = St.A ∧ c.cur = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    classical
    -- take the first halting time
    have hex : ∃ m : ℕ, run m = none := ⟨n, hn⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, run m = none ∧ ∀ k, k < m → run k ≠ none :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    cases m with
    | zero => simp [run_zero] at hm
    | succ m =>
      have h1 : run m ≠ none := hmin m (Nat.lt_succ_self m)
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp h1
      have hstep : step c = none := by
        have hrs := run_succ m
        rw [hc, hm] at hrs
        simpa [ostep] using hrs.symm
      exact ⟨m, c, hc, (step_eq_none_iff c).mp hstep⟩
  · rintro ⟨n, c, hc, h1, h2⟩
    refine ⟨n + 1, ?_⟩
    rw [run_succ, hc]
    simpa [ostep] using (step_eq_none_iff c).mpr ⟨h1, h2⟩

theorem iter_add (m n : ℕ) (o : Option Cfg) : iter (m + n) o = iter n (iter m o) := by
  induction m generalizing o with
  | zero => simp [iter]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    show iter (m + n) (ostep o) = _
    rw [ih (ostep o)]
    rfl

/-! ## Sweep rules

These four lemmas are the "macroscopic" moves out of which the whole
computation is built; they are what makes the description in `ANALYSIS.md`
precise.  Each one is proved by induction on the length of the block that the
head runs across. -/

/-- `A` running right across a block of `2`s rewrites them as `3`s. -/
theorem A_over_twos (k : ℕ) (a : Sym) (l r : List Sym) :
    iter (k + 1) (some ⟨St.A, l, 2, List.replicate k (2 : Sym) ++ a :: r⟩) =
      some ⟨St.A, List.replicate (k + 1) (3 : Sym) ++ l, a, r⟩ := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [show (k + 1 + 1) = 1 + (k + 1) by omega, iter_add]
    have h1 : iter 1 (some (⟨St.A, l, 2, List.replicate (k + 1) (2 : Sym) ++ a :: r⟩ : Cfg))
        = some ⟨St.A, (3 : Sym) :: l, 2, List.replicate k (2 : Sym) ++ a :: r⟩ := rfl
    rw [h1, ih]
    have h : (1 : ℕ) + (k + 1) = k + 2 := by omega
    rw [h]
    simp [List.replicate_succ', List.append_assoc]

/-- `B` running left across a block of `2`s rewrites them as `4`s. -/
theorem B_over_twos (k : ℕ) (a : Sym) (l r : List Sym) :
    iter (k + 1) (some ⟨St.B, List.replicate k (2 : Sym) ++ a :: l, 2, r⟩) =
      some ⟨St.B, l, a, List.replicate (k + 1) (4 : Sym) ++ r⟩ := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show (k + 1 + 1) = 1 + (k + 1) by omega, iter_add]
    have h1 : iter 1 (some (⟨St.B, List.replicate (k + 1) (2 : Sym) ++ a :: l, 2, r⟩ : Cfg))
        = some ⟨St.B, List.replicate k (2 : Sym) ++ a :: l, 2, (4 : Sym) :: r⟩ := rfl
    rw [h1, ih]
    have h : (1 : ℕ) + (k + 1) = k + 2 := by omega
    rw [h]
    simp [List.replicate_succ', List.append_assoc]

/-- Running right across a pair of `4`s costs two steps, leaves `2 0` behind
and returns the head to state `A`. -/
theorem A_over_two_fours (c : Sym) (l r : List Sym) :
    iter 2 (some ⟨St.A, l, 4, (4 : Sym) :: c :: r⟩) =
      some ⟨St.A, (0 : Sym) :: (2 : Sym) :: l, c, r⟩ := rfl

/-- **Overflow at the left end.**  `B` walking left across the block of `0`s
left by a saturated counter rewrites them as `2`s, reaches the `1`, turns it
into a `3`, and hands over to `A` one cell further to the left — this is how the
used part of the tape grows by one cell. -/
theorem frontier_overflow (k : ℕ) (a : Sym) (l r : List Sym) :
    iter (k + 2) (some ⟨St.B, List.replicate k (0 : Sym) ++ (1 : Sym) :: a :: l, 0, r⟩) =
      some ⟨St.A, l, a, (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ r⟩ := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show (k + 1 + 2) = 1 + (k + 2) by omega, iter_add]
    have h1 : iter 1
        (some (⟨St.B, List.replicate (k + 1) (0 : Sym) ++ (1 : Sym) :: a :: l, 0, r⟩ : Cfg))
        = some ⟨St.B, List.replicate k (0 : Sym) ++ (1 : Sym) :: a :: l, 0, (2 : Sym) :: r⟩ := rfl
    rw [h1, ih]
    simp [List.replicate_succ']

/-! ## The two decisive local patterns

Write a configuration as `… l₁ l₀ [cur] r₀ r₁ …`, the head being on `cur`.
The analysis in `ANALYSIS.md` shows that every approach of the head to a cell
containing `1` happens from the right, in state `A`, with the cell to the right
of the head containing `2`.  Exactly two things can then happen, and which one
happens is decided by the single symbol sitting between the `1` and the head. -/

theorem iter_four (o : Option Cfg) : iter 4 o = ostep (ostep (ostep (ostep o))) := by
  simp [iter]

/-- **The trap.**  If the head is in state `A` on a `0`, the cell to its left
contains `1` and the cell to its right contains `2`, the machine halts after
exactly four more steps — whatever the rest of the tape looks like. -/
theorem halt_trap (l r : List Sym) :
    iter 4 (some ⟨St.A, (1 : Sym) :: l, 0, (2 : Sym) :: r⟩) = none := by
  rw [iter_four]
  rfl

/-- **The escape.**  In the same situation but with a `4` instead of the `0`
under the head, the machine does *not* halt: after exactly four steps the `1`
has been overwritten by a `3` and the head has moved past it. -/
theorem no_halt_escape (a : Sym) (l r : List Sym) :
    iter 4 (some ⟨St.A, (1 : Sym) :: a :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.A, l, a, (3 : Sym) :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
  rw [iter_four]
  rfl

/-- The escape at the left end of the used part of the tape (`l = []`, so the
cell the head lands on is blank). -/
theorem no_halt_escape_blank (r : List Sym) :
    iter 4 (some ⟨St.A, [(1 : Sym)], 4, (2 : Sym) :: r⟩) =
      some ⟨St.A, [], 0, (3 : Sym) :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
  rw [iter_four]
  rfl

/-- A `1` under the head in state `B` is harmless: it is overwritten by a `3`
and the head steps left in state `A`. -/
theorem state_B_on_one (a : Sym) (l r : List Sym) :
    step ⟨St.B, a :: l, 1, r⟩ = some ⟨St.A, l, a, (3 : Sym) :: r⟩ := rfl

/-- **How a halt can be reached.**  If a step leads to a configuration in which
the head is in state `A` on a `1`, then before that step the head was on a cell
adjacent to that `1`, in one of exactly five local situations.  In particular a
halt is always caused by the head *moving onto* a cell that already contains a
`1`. -/
theorem pre_halt_shape (c d : Cfg) (h : step c = some d) (hA : d.st = St.A) (h1 : d.cur = 1) :
    (c.st = St.A ∧ c.cur = 3 ∧ ∃ l, c.left = 1 :: l) ∨
    (c.st = St.B ∧ c.cur = 1 ∧ ∃ l, c.left = 1 :: l) ∨
    (c.st = St.A ∧ c.cur = 2 ∧ ∃ r, c.right = 1 :: r) ∨
    (c.st = St.B ∧ c.cur = 3 ∧ ∃ r, c.right = 1 :: r) ∨
    (c.st = St.B ∧ c.cur = 4 ∧ ∃ r, c.right = 1 :: r) := by
  obtain ⟨s, l, x, r⟩ := c
  cases s <;> cases x <;> cases l <;> cases r <;>
    simp only [step, Cfg.wL, Cfg.wR] at h <;>
    first
      | (injection h with h; subst h; simp_all [OfNat.ofNat])
      | simp at h

/-! ## A verified lower bound on the running time -/

/-- The machine is still running after `10^8` steps (checked by compiled
evaluation of the simulator defined above). -/
theorem run_hundred_million_isSome : (run 100000000).isSome = true := by
  native_decide

/-- **The machine does not halt during its first `10^8` steps.** -/
theorem not_halted_before_hundred_million {n : ℕ} (hn : n ≤ 100000000) : run n ≠ none := by
  intro h
  have hb := run_hundred_million_isSome
  rw [run_eq_none_of_le hn h] at hb
  simp at hb

end TM2x5
