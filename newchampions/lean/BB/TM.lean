/-
  BB/TM.lean
  Exact, axiom-free operational semantics for n-state, m-symbol Turing Machines
  matching the standard bbchallenge.org Busy Beaver conventions.
-/

namespace BB

inductive Dir where
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

/-- Transition output: write symbol, move direction, next state (`none` = halt `Z`). -/
structure Action where
  write : Nat
  dir   : Dir
  next  : Option Nat
  deriving DecidableEq, Repr

/-- A Turing machine transition table: `(state, symbol) -> Option Action`. -/
abbrev TM := Nat → Nat → Option Action

/-- Certificate that `tm` belongs to domain `BB(nStates, nSyms)`. -/
def ValidTM (nStates nSyms : Nat) (tm : TM) : Prop :=
  (∀ s sym, s < nStates → sym < nSyms →
    match tm s sym with
    | none => True
    | some act =>
        act.write < nSyms ∧
        match act.next with
        | none => True
        | some s' => s' < nStates) ∧
  (∀ s sym, (nStates ≤ s ∨ nSyms ≤ sym) → tm s sym = none)

/-- Machine configuration: state (`none` = halted), reversed left tape, head symbol, right tape.
    Empty list `[]` represents an infinite tail of blank (`0`) symbols. -/
structure Config where
  st    : Option Nat
  left  : List Nat
  cur   : Nat
  right : List Nat
  deriving DecidableEq, Repr

/-- Blank initial configuration `0^∞ A> 0^∞` (state A = 0). -/
def initConfig : Config :=
  { st := some 0, left := [], cur := 0, right := [] }

/-- Push symbol onto a blank-terminated tape half, maintaining canonical blank tails. -/
def cons0 (w : Nat) (xs : List Nat) : List Nat :=
  match w, xs with
  | 0, [] => []
  | w, xs => w :: xs

/-- Single Turing machine step. Returns `none` if already halted (`st = none`).
    An undefined transition (`tm q cur = none`) halts in 1 step (standard TNF `---`). -/
def step (tm : TM) (c : Config) : Option Config :=
  match c.st with
  | none => none
  | some q =>
    match tm q c.cur with
    | none => some { c with st := none }
    | some act =>
      match act.dir with
      | Dir.L =>
        match c.left with
        | [] => some { st := act.next, left := [], cur := 0, right := cons0 act.write c.right }
        | a :: l' => some { st := act.next, left := l', cur := a, right := cons0 act.write c.right }
      | Dir.R =>
        match c.right with
        | [] => some { st := act.next, left := cons0 act.write c.left, cur := 0, right := [] }
        | a :: r' => some { st := act.next, left := cons0 act.write c.left, cur := a, right := r' }

/-- Exact `t`-step execution. Returns `none` if the machine halted strictly before step `t`. -/
def steps (tm : TM) : Nat → Config → Option Config
  | 0, c => some c
  | t + 1, c =>
    match step tm c with
    | none => none
    | some c' => steps tm t c'

/-- Machine `tm` halts from `c0` in **exact** `t` steps. -/
def HaltsIn (tm : TM) (c0 : Config) (t : Nat) : Prop :=
  ∃ cf, steps tm t c0 = some cf ∧ cf.st = none

/-- Repeat symbol `s` `n` times and append `xs`. -/
def rep (n : Nat) (s : Nat) (xs : List Nat) : List Nat :=
  match n with
  | 0 => xs
  | k + 1 => s :: rep k s xs

/-! ### Basic Execution Lemmas -/

theorem steps_zero (tm : TM) (c : Config) : steps tm 0 c = some c := rfl

theorem steps_one (tm : TM) (c1 c2 : Config) (h : step tm c1 = some c2) :
    steps tm 1 c1 = some c2 := by
  simp [steps, h]

theorem steps_add (tm : TM) (t1 t2 : Nat) (c1 c2 c3 : Config)
    (h1 : steps tm t1 c1 = some c2) (h2 : steps tm t2 c2 = some c3) :
    steps tm (t1 + t2) c1 = some c3 := by
  induction t1 generalizing c1 with
  | zero =>
    simp [steps] at h1
    subst h1
    simpa [Nat.zero_add] using h2
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [steps] at h1 ⊢
    cases hs : step tm c1 with
    | none => rw [hs] at h1; contradiction
    | some cm =>
      rw [hs] at h1
      exact ih cm h1

theorem steps_succ (tm : TM) (t : Nat) (c1 c2 c3 : Config)
    (h1 : step tm c1 = some c2) (h2 : steps tm t c2 = some c3) :
    steps tm (t + 1) c1 = some c3 := by
  simp [steps, h1, h2]

theorem rep_zero (s : Nat) (xs : List Nat) : rep 0 s xs = xs := rfl

theorem rep_succ (n s : Nat) (xs : List Nat) : rep (n + 1) s xs = s :: rep n s xs := rfl

theorem rep_add (a b s : Nat) (xs : List Nat) :
    rep (a + b) s xs = rep a s (rep b s xs) := by
  induction a with
  | zero => simp [rep]
  | succ k ih =>
    rw [Nat.succ_add, rep_succ, rep_succ, ih]

theorem cons0_succ (w : Nat) (xs : List Nat) : cons0 (w + 1) xs = (w + 1) :: xs := rfl

theorem cons0_cons (w x : Nat) (xs : List Nat) : cons0 w (x :: xs) = w :: x :: xs := by
  cases w <;> rfl

theorem cons0_zero_nil : cons0 0 [] = [] := rfl

/-! ### Sanity Checks: BB(2,2) = 6 and BB(3,2) = 21 -/

private def bb22 : TM
  | 0, 0 => some ⟨1, Dir.R, some 1⟩
  | 0, 1 => some ⟨1, Dir.L, some 1⟩
  | 1, 0 => some ⟨1, Dir.L, some 0⟩
  | 1, 1 => some ⟨1, Dir.R, none⟩
  | _, _ => none

theorem bb22_halts_6 : HaltsIn bb22 initConfig 6 :=
  ⟨{ st := none, left := [1, 1], cur := 1, right := [1] }, rfl, rfl⟩

private def bb32 : TM
  | 0, 0 => some ⟨1, Dir.R, some 1⟩
  | 0, 1 => some ⟨1, Dir.R, none⟩
  | 1, 0 => some ⟨1, Dir.L, some 1⟩
  | 1, 1 => some ⟨0, Dir.R, some 2⟩
  | 2, 0 => some ⟨1, Dir.L, some 2⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | _, _ => none

theorem bb32_halts_21 : HaltsIn bb32 initConfig 21 :=
  ⟨{ st := none, left := [1, 1], cur := 1, right := [1, 1] }, rfl, rfl⟩

end BB
