/-
  Self-contained Lean 4 formalization of the BB(2,5) machine

      1RB---3RA2LA2RB_2LB3LA4LB4RA0RA

  This file deliberately does NOT claim that the machine halts or that it
  runs forever.  The global question is open in the public record.  What is
  proved here is:

  * the halting criterion (the only undefined transition is A reading 1);
  * the two four-step local rules that decide a frontier encounter;
  * the invariant that no cell strictly to the right of the head is a 1;
  * a compiled-evaluation certificate that the machine is still running after
    100,000,000 steps.

  The file uses only Lean's core library, so it can be checked with the
  installed Lean 4.35 toolchain without Mathlib.
-/

namespace TM25

/-- The two states. -/
inductive St
  | A
  | B
  deriving DecidableEq, Repr

/-- The five tape symbols; `s0` is blank. -/
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

/-- A configuration: state, cells immediately left of the head (nearest
first), the cell under the head, and cells immediately right (nearest first). -/
structure Cfg where
  st : St
  left : List Sym
  cur : Sym
  right : List Sym
  deriving DecidableEq, Repr

namespace Cfg

/-- Write `w`, move left, enter `s`. -/
def wL (c : Cfg) (w : Sym) (s : St) : Cfg :=
  match c.left with
  | [] => ⟨s, [], 0, w :: c.right⟩
  | x :: xs => ⟨s, xs, x, w :: c.right⟩

/-- Write `w`, move right, enter `s`. -/
def wR (c : Cfg) (w : Sym) (s : St) : Cfg :=
  match c.right with
  | [] => ⟨s, w :: c.left, 0, []⟩
  | x :: xs => ⟨s, w :: c.left, x, xs⟩

end Cfg

/-- One literal transition; `none` is the halt transition. -/
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

/-- One step lifted to `Option`; once halted, stays halted. -/
def ostep (o : Option Cfg) : Option Cfg := o.bind step

/-- `iter n` applies `ostep` `n` times. -/
def iter : Nat → Option Cfg → Option Cfg
  | 0, o => o
  | n + 1, o => iter n (ostep o)

/-- Blank-tape initial configuration. -/
def init : Cfg := ⟨St.A, [], 0, []⟩

/-- Configuration after `n` steps. -/
def run (n : Nat) : Option Cfg := iter n (some init)

/-- The machine halts. -/
def Halts : Prop := ∃ n : Nat, run n = none

/-! ## Elementary properties -/

@[simp] theorem run_zero : run 0 = some init := rfl

@[simp] theorem ostep_none : ostep none = none := rfl

/-- The only halting transition is `A` reading `1`. -/
theorem step_eq_none_iff (c : Cfg) :
    step c = none ↔ (c.st = St.A ∧ c.cur = 1) := by
  rcases c with ⟨s, l, x, r⟩
  cases s <;> cases x <;> simp [step] <;> rfl

theorem no_halt_in_B (c : Cfg) (h : c.st = St.B) : step c ≠ none := by
  simp [step_eq_none_iff, h]

theorem iter_succ (n : Nat) (o : Option Cfg) :
    iter (n + 1) o = ostep (iter n o) := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih => simpa [iter] using ih (ostep o)

theorem run_succ (n : Nat) : run (n + 1) = ostep (run n) :=
  iter_succ n _

/-- Once halted, always halted. -/
theorem run_eq_none_of_le {m n : Nat} (hmn : m ≤ n) (h : run m = none) :
    run n = none := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm
      exact h
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [run_succ, ih hle]
        rfl
      · have hm : m = n + 1 := Nat.le_antisymm hmn hge
        subst hm
        exact h

/-- A `1` under the head in state `B` is harmless. -/
theorem state_B_on_one (a : Sym) (l r : List Sym) :
    step ⟨St.B, a :: l, 1, r⟩ = some ⟨St.A, l, a, (3 : Sym) :: r⟩ := rfl

/-- The trap: `A` on `0`, with a `1` immediately to the left and a `2` to
the right, halts in exactly four steps. -/
theorem halt_trap (l r : List Sym) :
    iter 4 (some ⟨St.A, (1 : Sym) :: l, 0, (2 : Sym) :: r⟩) = none := by
  rfl

/-- The escape: the same shape but with `4` under the head does not halt. -/
theorem no_halt_escape (a : Sym) (l r : List Sym) :
    iter 4 (some ⟨St.A, (1 : Sym) :: a :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.A, l, a, (3 : Sym) :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
  rfl

/-- A concrete prefix, useful as a sanity check against external simulators. -/
theorem run_seven :
    run 7 = some ⟨St.B, [1, 3, 4, 1], 0, []⟩ := by
  rfl

/-! ## No `1` strictly right of the head -/

/-- No cell strictly to the right of the head holds a `1`. -/
def NoOneRight (c : Cfg) : Prop := (1 : Sym) ∉ c.right

theorem wL_right (c : Cfg) (w : Sym) (s : St) :
    (c.wL w s).right = w :: c.right := by
  unfold Cfg.wL
  cases c.left <;> rfl

theorem wR_right (c : Cfg) (w : Sym) (s : St) :
    (c.wR w s).right = c.right.tail := by
  unfold Cfg.wR
  cases c.right <;> rfl

theorem noOneRight_init : NoOneRight init := by
  simp [NoOneRight, init]

/-- The invariant is preserved: the only transition writing a `1` moves right,
and every left-moving transition writes `0`, `2`, `3`, or `4`. -/
theorem noOneRight_step {c d : Cfg} (h : NoOneRight c) (hs : step c = some d) :
    NoOneRight d := by
  have keyL : ∀ (w : Sym) (st : St), w ≠ 1 → NoOneRight (c.wL w st) := by
    intro w st hw
    simp only [NoOneRight, wL_right, List.mem_cons, not_or]
    exact ⟨fun hEq => hw hEq.symm, h⟩
  have keyR : ∀ (w : Sym) (st : St), NoOneRight (c.wR w st) := by
    intro w st
    simp only [NoOneRight, wR_right]
    intro hmem
    exact h (List.mem_of_mem_tail hmem)
  unfold step at hs
  cases hst : c.st <;> cases hcur : c.cur <;> rw [hst, hcur] at hs <;>
    simp only [Option.some.injEq] at hs <;>
    first
      | exact absurd hs (by simp)
      | (subst hs; first
          | exact keyR _ _
          | exact keyL _ _ (by decide))

/-- Every reachable configuration has no `1` strictly right of the head. -/
theorem noOneRight_run : ∀ (n : Nat) (c : Cfg), run n = some c → NoOneRight c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      rw [run_zero] at hc
      cases hc
      exact noOneRight_init
  | succ n ih =>
      intro c hc
      rw [run_succ] at hc
      cases hr : run n with
      | none =>
          rw [hr] at hc
          simp [ostep] at hc
      | some c' =>
          rw [hr] at hc
          exact noOneRight_step (ih c' hr) hc

/-! ## A checked finite lower bound -/

/-- Compiled evaluation reaches 100,000,000 steps without halting.  This is a
finite certificate only; it is not a nonhalting proof. -/
theorem run_hundred_million_isSome : (run 100000000).isSome = true := by
  native_decide

/-- The machine has not halted during its first 100,000,000 steps. -/
theorem not_halted_before_hundred_million {n : Nat} (hn : n ≤ 100000000) :
    run n ≠ none := by
  intro h
  have hb := run_hundred_million_isSome
  rw [run_eq_none_of_le hn h] at hb
  simp at hb


/-! ## Missing interface definitions from the archive -/

/-- The head is on the first cell of `xs`; cells beyond are blank. -/
def onFirst (st : St) (l : List Sym) : List Sym → Cfg
  | [] => ⟨st, l, 0, []⟩
  | x :: xs => ⟨st, l, x, xs⟩

/-- The head is on the first cell of `L`, with `R` to its right. -/
def cfgAt (st : St) : List Sym → List Sym → Cfg
  | [], R => ⟨st, [], 0, R⟩
  | a :: L, R => ⟨st, L, a, R⟩

theorem iter_add (m n : Nat) (o : Option Cfg) :
    iter (m + n) o = iter n (iter m o) := by
  induction m generalizing o with
  | zero => simp [iter]
  | succ m ih =>
      have h : m + 1 + n = (m + n) + 1 := by omega
      rw [h]
      show iter (m + n) (ostep o) = _
      rw [ih (ostep o)]
      rfl

/-- `A` running right across a block of `2`s rewrites them as `3`s. -/
theorem A_over_twos (k : Nat) (a : Sym) (l r : List Sym) :
    iter (k + 1) (some ⟨St.A, l, 2, List.replicate k (2 : Sym) ++ a :: r⟩) =
      some ⟨St.A, List.replicate (k + 1) (3 : Sym) ++ l, a, r⟩ := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
      rw [show (k + 1 + 1) = 1 + (k + 1) by omega, iter_add]
      have h1 : iter 1
          (some (⟨St.A, l, 2, List.replicate (k + 1) (2 : Sym) ++ a :: r⟩ : Cfg)) =
          some ⟨St.A, (3 : Sym) :: l, 2, List.replicate k (2 : Sym) ++ a :: r⟩ := rfl
      rw [h1, ih]
      have h : (1 : Nat) + (k + 1) = k + 2 := by omega
      rw [h]
      simp [List.replicate_succ', List.append_assoc]

/-! ## Counter values and the increment -/

def digitVal : Sym → Nat
  | Sym.s3 => 0
  | Sym.s4 => 1
  | Sym.s0 => 2
  | _ => 0

def IsDigit (s : Sym) : Prop := s = 3 ∨ s = 4 ∨ s = 0

def counterValue : List Sym → Nat
  | [] => 0
  | d :: ds => digitVal d + 3 * counterValue ds

@[simp] theorem counterValue_nil : counterValue [] = 0 := rfl

@[simp] theorem counterValue_cons (d : Sym) (ds : List Sym) :
    counterValue (d :: ds) = digitVal d + 3 * counterValue ds := rfl

def incr : List Sym → List Sym
  | [] => []
  | Sym.s3 :: ds => (4 : Sym) :: ds
  | Sym.s4 :: ds => (0 : Sym) :: ds
  | Sym.s0 :: ds => (3 : Sym) :: incr ds
  | d :: ds => d :: ds

def Saturated : List Sym → Prop
  | [] => True
  | d :: ds => d = 0 ∧ Saturated ds

theorem counterValue_incr (ds : List Sym) (hd : ∀ s ∈ ds, IsDigit s)
    (hs : ¬ Saturated ds) : counterValue (incr ds) = counterValue ds + 1 := by
  induction ds with
  | nil => exact absurd trivial hs
  | cons d ds ih =>
      have hdd : IsDigit d := hd d (List.mem_cons_self ..)
      have hds : ∀ s ∈ ds, IsDigit s := fun s hsm => hd s (List.mem_cons_of_mem _ hsm)
      rcases hdd with h | h | h <;> subst h
      · simp [incr, counterValue, digitVal]; omega
      · simp [incr, counterValue, digitVal]; omega
      · have hs' : ¬ Saturated ds := by
          intro hsat
          exact hs ⟨rfl, hsat⟩
        simp [incr, counterValue, digitVal, ih hds hs']
        omega

def incrCost : List Sym → Nat
  | Sym.s3 :: _ => 1
  | Sym.s4 :: _ => 1
  | Sym.s0 :: ds => incrCost ds + 2
  | _ => 0

theorem counter_increment :
    ∀ (d : Sym) (ds : List Sym), IsDigit d → (∀ s ∈ ds, IsDigit s) →
      ¬ Saturated (d :: ds) → ∀ (l r' : List Sym) (r0 : Sym),
        iter (incrCost (d :: ds)) (some ⟨St.B, ds ++ l, d, r0 :: r'⟩) =
          some ⟨St.A, incr (d :: ds) ++ l, r0, r'⟩ := by
  intro d ds
  induction ds generalizing d with
  | nil =>
      intro hd _ hs l r' r0
      rcases hd with h | h | h <;> subst h
      · rfl
      · rfl
      · exact absurd ⟨rfl, trivial⟩ hs
  | cons e ds ih =>
      intro hd hds hs l r' r0
      rcases hd with h | h | h <;> subst h
      · rfl
      · rfl
      · have he : IsDigit e := hds e (List.mem_cons_self ..)
        have hes : ∀ s ∈ ds, IsDigit s := fun s hsm => hds s (List.mem_cons_of_mem _ hsm)
        have hs' : ¬ Saturated (e :: ds) := fun hsat => hs ⟨rfl, hsat⟩
        have h1 : iter 1 (some (⟨St.B, (e :: ds) ++ l, 0, r0 :: r'⟩ : Cfg)) =
            some ⟨St.B, ds ++ l, e, (2 : Sym) :: r0 :: r'⟩ := rfl
        have hcost : incrCost ((0 : Sym) :: e :: ds) = 1 + (incrCost (e :: ds) + 1) := by
          simp [incrCost]
          omega
        rw [hcost, iter_add, h1, iter_add, ih e he hes hs' l (r0 :: r') 2]
        have h2 : iter 1 (some (⟨St.A, incr (e :: ds) ++ l, 2, r0 :: r'⟩ : Cfg)) =
            some ⟨St.A, (3 : Sym) :: (incr (e :: ds) ++ l), r0, r'⟩ := rfl
        rw [h2]
        simp [incr]

theorem frontier_overflow_blank (k : Nat) (r : List Sym) :
    iter (k + 2) (some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, r⟩) =
      some ⟨St.A, [], 0, (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ r⟩ := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
      rw [show (k + 1 + 2) = 1 + (k + 2) by omega, iter_add]
      have h1 : iter 1
          (some (⟨St.B, List.replicate (k + 1) (0 : Sym) ++ [1], 0, r⟩ : Cfg)) =
          some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, (2 : Sym) :: r⟩ := rfl
      rw [h1, ih]
      simp [List.replicate_succ']

theorem counter_overflow (k : Nat) (r0 : Sym) (r' : List Sym) :
    iter (2 * k + 5) (some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, r0 :: r'⟩) =
      some ⟨St.A, List.replicate (k + 1) (3 : Sym) ++ [(4 : Sym), (1 : Sym)], r0, r'⟩ := by
  have hsplit : 2 * k + 5 = (k + 2) + (2 + (k + 1)) := by omega
  rw [hsplit, iter_add, frontier_overflow_blank k (r0 :: r')]
  rw [iter_add]
  have h2 : iter 2 (some (⟨St.A, [], 0,
      (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ r0 :: r'⟩ : Cfg)) =
      some ⟨St.A, [(4 : Sym), (1 : Sym)], 2, List.replicate k (2 : Sym) ++ r0 :: r'⟩ := by
    rw [List.replicate_succ]
    rfl
  rw [h2, A_over_twos k r0 [(4 : Sym), (1 : Sym)] r']

theorem counterValue_saturated (k : Nat) :
    counterValue (List.replicate k (0 : Sym)) = 3 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by decide)
      rw [List.replicate_succ, counterValue_cons, ih]
      show 2 + 3 * (3 ^ k - 1) = 3 ^ (k + 1) - 1
      rw [Nat.pow_succ]
      omega

theorem counterValue_after_overflow (k : Nat) :
    counterValue (List.replicate (k + 1) (3 : Sym) ++ [(4 : Sym)]) = 3 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, counterValue_cons, ih]
      show 0 + 3 * 3 ^ (k + 1) = 3 ^ (k + 1 + 1)
      rw [Nat.pow_succ]
      omega

/-! ## Cascades -/

inductive Mode
  | P
  | Q
  deriving DecidableEq, Repr

def Mode.sym : Mode → Sym
  | Mode.P => 2
  | Mode.Q => 3

theorem cascade_P_three (c : Sym) (l r : List Sym) :
    iter 1 (some ⟨St.A, c :: l, 3, (2 : Sym) :: r⟩) =
      some ⟨St.A, l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl

theorem cascade_P_zero (c : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, c :: l, 0, (2 : Sym) :: r⟩) =
      some ⟨St.A, l, c, (3 : Sym) :: (4 : Sym) :: r⟩ := rfl

theorem cascade_Q_three (c : Sym) (l r : List Sym) :
    iter 1 (some ⟨St.A, c :: l, 3, (3 : Sym) :: r⟩) =
      some ⟨St.A, l, c, (2 : Sym) :: (3 : Sym) :: r⟩ := rfl

theorem cascade_Q_two (c : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, c :: l, 2, (3 : Sym) :: r⟩) =
      some ⟨St.A, l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl

theorem cascade_halts_on_one (l r : List Sym) :
    iter 1 (some ⟨St.A, l, 1, r⟩) = none := rfl

theorem cascade_P_four_stops (c : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, c :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r⟩ := rfl

theorem cascade_P_two_stops (l r : List Sym) :
    iter 1 (some ⟨St.A, l, 2, (2 : Sym) :: r⟩) =
      some ⟨St.A, (3 : Sym) :: l, 2, r⟩ := rfl

theorem cascade_Q_zero_stops (l r : List Sym) (x : Sym) :
    iter 2 (some ⟨St.A, l, 0, (3 : Sym) :: x :: r⟩) =
      some ⟨St.A, (4 : Sym) :: (1 : Sym) :: l, x, r⟩ := rfl

theorem cascade_Q_four_stops (l r : List Sym) (x : Sym) :
    iter 2 (some ⟨St.A, l, 4, (3 : Sym) :: x :: r⟩) =
      some ⟨St.A, (4 : Sym) :: (2 : Sym) :: l, x, r⟩ := rfl

inductive Cross : Mode → Sym → List Sym → Prop
  | haltP {w : List Sym} : Cross Mode.P 1 w
  | haltQ {w : List Sym} : Cross Mode.Q 1 w
  | P3 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.P 3 (c :: w)
  | P0 {c : Sym} {w : List Sym} : Cross Mode.Q c w → Cross Mode.P 0 (c :: w)
  | Q3 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.Q 3 (c :: w)
  | Q2 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.Q 2 (c :: w)

theorem cross_halts {m : Mode} {c : Sym} {w : List Sym} (h : Cross m c w) :
    ∀ l r : List Sym, ∃ n, iter n (some ⟨St.A, w ++ l, c, m.sym :: r⟩) = none := by
  induction h with
  | haltP => exact fun l r => ⟨1, rfl⟩
  | haltQ => exact fun l r => ⟨1, rfl⟩
  | @P3 c w _ ih =>
      intro l r
      obtain ⟨n, hn⟩ := ih l ((2 : Sym) :: r)
      refine ⟨1 + n, ?_⟩
      rw [iter_add]
      have h1 : iter 1 (some (⟨St.A, (c :: w) ++ l, 3, Mode.P.sym :: r⟩ : Cfg)) =
          some ⟨St.A, w ++ l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
      rw [h1]
      exact hn
  | @P0 c w _ ih =>
      intro l r
      obtain ⟨n, hn⟩ := ih l ((4 : Sym) :: r)
      refine ⟨3 + n, ?_⟩
      rw [iter_add]
      have h1 : iter 3 (some (⟨St.A, (c :: w) ++ l, 0, Mode.P.sym :: r⟩ : Cfg)) =
          some ⟨St.A, w ++ l, c, (3 : Sym) :: (4 : Sym) :: r⟩ := rfl
      rw [h1]
      exact hn
  | @Q3 c w _ ih =>
      intro l r
      obtain ⟨n, hn⟩ := ih l ((3 : Sym) :: r)
      refine ⟨1 + n, ?_⟩
      rw [iter_add]
      have h1 : iter 1 (some (⟨St.A, (c :: w) ++ l, 3, Mode.Q.sym :: r⟩ : Cfg)) =
          some ⟨St.A, w ++ l, c, (2 : Sym) :: (3 : Sym) :: r⟩ := rfl
      rw [h1]
      exact hn
  | @Q2 c w _ ih =>
      intro l r
      obtain ⟨n, hn⟩ := ih l ((2 : Sym) :: r)
      refine ⟨3 + n, ?_⟩
      rw [iter_add]
      have h1 : iter 3 (some (⟨St.A, (c :: w) ++ l, 2, Mode.Q.sym :: r⟩ : Cfg)) =
          some ⟨St.A, w ++ l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
      rw [h1]
      exact hn

/-! ## The Cantor criterion -/

/-- No two consecutive cells contain `0` (the digit `2`). -/
def NoAdjacentZeros : List Sym → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: u => ¬ (a = 0 ∧ b = 0) ∧ NoAdjacentZeros (b :: u)

theorem noAdjacentZeros_singleton (a : Sym) : NoAdjacentZeros [a] := trivial

theorem noAdjacentZeros_cons_cons {a b : Sym} {u : List Sym} :
    NoAdjacentZeros (a :: b :: u) ↔
      ¬ (a = 0 ∧ b = 0) ∧ NoAdjacentZeros (b :: u) := Iff.rfl

theorem cantor_cross_aux : ∀ (u : List Sym) (c : Sym), (c = 3 ∨ c = 0) →
    (∀ s ∈ u, s = 3 ∨ s = 0) → NoAdjacentZeros (c :: u) →
    Cross Mode.P c (u ++ [1]) ∧ (c = 3 → Cross Mode.Q c (u ++ [1])) := by
  intro u
  induction u with
  | nil =>
      intro c hc _ _
      rcases hc with h | h <;> subst h
      · exact ⟨Cross.P3 Cross.haltP, fun _ => Cross.Q3 Cross.haltP⟩
      · exact ⟨Cross.P0 Cross.haltQ, fun h => by simp at h⟩
  | cons d u ih =>
      intro c hc hu hno
      have hd : d = 3 ∨ d = 0 := hu d (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u, s = 3 ∨ s = 0 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      have hsplit := noAdjacentZeros_cons_cons.mp hno
      have hIH := ih d hd hu' hsplit.2
      rcases hc with h | h <;> subst h
      · exact ⟨Cross.P3 hIH.1, fun _ => Cross.Q3 hIH.1⟩
      · have hd3 : d = 3 := by
          rcases hd with h | h
          · exact h
          · exact absurd ⟨rfl, h⟩ hsplit.1
        exact ⟨Cross.P0 (hIH.2 hd3), fun h => by simp at h⟩

theorem cantor_cross (u : List Sym) (c : Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) : Cross Mode.P c (u ++ [1]) :=
  (cantor_cross_aux u c hc hu hno).1

theorem cascade_halt_over_cantor_block (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n, iter n (some ⟨St.A, u ++ (1 : Sym) :: l, c, (2 : Sym) :: r⟩) = none := by
  have h := cross_halts (cantor_cross u c hc hu hno) l r
  simpa [Mode.sym] using h

theorem not_isDigit_one : ¬ IsDigit (1 : Sym) := by
  rintro (h | h | h) <;> exact Sym.noConfusion h

theorem not_isDigit_two : ¬ IsDigit (2 : Sym) := by
  rintro (h | h | h) <;> exact Sym.noConfusion h

theorem cross_digits_aux : ∀ (u : List Sym) (c : Sym), IsDigit c → (∀ s ∈ u, IsDigit s) →
    (Cross Mode.P c (u ++ [1]) →
      (c = 3 ∨ c = 0) ∧ (∀ s ∈ u, s = 3 ∨ s = 0) ∧ NoAdjacentZeros (c :: u)) ∧
    (Cross Mode.Q c (u ++ [1]) →
      c = 3 ∧ (∀ s ∈ u, s = 3 ∨ s = 0) ∧ NoAdjacentZeros (c :: u)) := by
  intro u
  induction u with
  | nil =>
      intro c hc _
      constructor
      · intro h
        cases h with
        | haltP => exact absurd hc not_isDigit_one
        | P3 _ => exact ⟨Or.inl rfl, by simp, noAdjacentZeros_singleton _⟩
        | P0 _ => exact ⟨Or.inr rfl, by simp, noAdjacentZeros_singleton _⟩
      · intro h
        cases h with
        | haltQ => exact absurd hc not_isDigit_one
        | Q3 _ => exact ⟨rfl, by simp, noAdjacentZeros_singleton _⟩
        | Q2 _ => exact absurd hc not_isDigit_two
  | cons d u ih =>
      intro c hc hu
      have hd : IsDigit d := hu d (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u, IsDigit s := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      have hIH := ih d hd hu'
      constructor
      · intro h
        cases h with
        | haltP => exact absurd hc not_isDigit_one
        | P3 h' =>
            obtain ⟨hd', hus, hch⟩ := hIH.1 h'
            refine ⟨Or.inl rfl, ?_, ?_⟩
            · intro s hs
              rcases List.mem_cons.mp hs with h | h
              · exact h ▸ hd'
              · exact hus s h
            · exact ⟨by simp, hch⟩
        | P0 h' =>
            obtain ⟨hd3, hus, hch⟩ := hIH.2 h'
            refine ⟨Or.inr rfl, ?_, ?_⟩
            · intro s hs
              rcases List.mem_cons.mp hs with h | h
              · exact h ▸ Or.inl hd3
              · exact hus s h
            · refine ⟨?_, hch⟩
              rintro ⟨-, h0⟩
              rw [hd3] at h0
              simp at h0
      · intro h
        cases h with
        | haltQ => exact absurd hc not_isDigit_one
        | Q3 h' =>
            obtain ⟨hd', hus, hch⟩ := hIH.1 h'
            refine ⟨rfl, ?_, ?_⟩
            · intro s hs
              rcases List.mem_cons.mp hs with h | h
              · exact h ▸ hd'
              · exact hus s h
            · exact ⟨by simp, hch⟩
        | Q2 _ => exact absurd hc not_isDigit_two

theorem cross_digits_iff (u : List Sym) (c : Sym) (hc : IsDigit c)
    (hu : ∀ s ∈ u, IsDigit s) :
    Cross Mode.P c (u ++ [1]) ↔
      ((c = 3 ∨ c = 0) ∧ (∀ s ∈ u, s = 3 ∨ s = 0) ∧ NoAdjacentZeros (c :: u)) := by
  refine ⟨(cross_digits_aux u c hc hu).1, ?_⟩
  rintro ⟨h1, h2, h3⟩
  exact cantor_cross u c h1 h2 h3

def bgPairs : Nat → List Sym
  | 0 => []
  | k + 1 => (0 : Sym) :: (2 : Sym) :: bgPairs k

theorem cross_bg : ∀ (k : Nat) {c : Sym} {w : List Sym}, Cross Mode.P c w →
    Cross Mode.P 0 ((2 : Sym) :: bgPairs k ++ c :: w) := by
  intro k
  induction k with
  | zero => intro c w h; exact Cross.P0 (Cross.Q2 h)
  | succ k ih =>
      intro c w h
      have := ih h
      simpa [bgPairs] using Cross.P0 (Cross.Q2 this)

theorem cascade_birth (x : Sym) (l : List Sym) :
    iter 3 (some ⟨St.A, x :: l, 0, []⟩) = some ⟨St.A, l, x, [(3 : Sym), (2 : Sym)]⟩ := rfl

theorem halt_of_cantor_to_right_end (u l : List Sym)
    (hu : ∀ s ∈ u, s = 3 ∨ s = 0) (hno : NoAdjacentZeros ((3 : Sym) :: u)) :
    ∃ n, iter n (some ⟨St.A, ((3 : Sym) :: u) ++ (1 : Sym) :: l, 0, []⟩) = none := by
  obtain ⟨n, hn⟩ :=
    cross_halts ((cantor_cross_aux u 3 (Or.inl rfl) hu hno).2 rfl) l [(2 : Sym)]
  refine ⟨3 + n, ?_⟩
  rw [iter_add]
  have h1 : iter 3 (some (⟨St.A, ((3 : Sym) :: u) ++ (1 : Sym) :: l, 0, []⟩ : Cfg)) =
      some ⟨St.A, u ++ (1 : Sym) :: l, 3, [(3 : Sym), (2 : Sym)]⟩ := rfl
  rw [h1]
  simpa [Mode.sym] using hn

theorem halt_of_bg_then_cantor (k : Nat) (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n, iter n (some ⟨St.A, (2 : Sym) :: bgPairs k ++ c :: u ++ (1 : Sym) :: l, 0,
      (2 : Sym) :: r⟩) = none := by
  have h := cross_halts (cross_bg k (cantor_cross u c hc hu hno)) l r
  simpa [Mode.sym] using h

example : iter 10 (some (⟨St.A, [(0 : Sym), 3, 0, 3, (1 : Sym), 2, 2], 3, [(2 : Sym)]⟩ : Cfg)) = none := rfl

example : (iter 30 (some (⟨St.A, [(0 : Sym), 3, 4, 3, (1 : Sym), 2, 2], 3, [(2 : Sym)]⟩ : Cfg))).isSome = true := rfl

theorem cantor_traverse : ∀ (u : List Sym) (c : Sym), (c = 3 ∨ c = 0) →
    (∀ s ∈ u, s = 3 ∨ s = 0) → NoAdjacentZeros (c :: u) → ∀ (x : Sym) (l r : List Sym),
    (∃ (n : Nat) (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ x :: l, c, (2 : Sym) :: r⟩) = some ⟨St.A, l, x, m'.sym :: r'⟩) ∧
    (c = 3 → ∃ (n : Nat) (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ x :: l, c, (3 : Sym) :: r⟩) = some ⟨St.A, l, x, m'.sym :: r'⟩) := by
  intro u
  induction u with
  | nil =>
      intro c hc _ _ x l r
      rcases hc with h | h <;> subst h
      · refine ⟨⟨1, Mode.P, (2 : Sym) :: r, rfl⟩, fun _ => ⟨1, Mode.P, (3 : Sym) :: r, rfl⟩⟩
      · exact ⟨⟨3, Mode.Q, (4 : Sym) :: r, rfl⟩, fun h => by simp at h⟩
  | cons d u ih =>
      intro c hc hu hno x l r
      have hd : d = 3 ∨ d = 0 := hu d (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u, s = 3 ∨ s = 0 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      have hsplit := noAdjacentZeros_cons_cons.mp hno
      have key : ∀ (r'' : List Sym),
          (∃ (n : Nat) (m' : Mode) (r' : List Sym),
            iter n (some (⟨St.A, u ++ x :: l, d, (2 : Sym) :: r''⟩ : Cfg)) =
              some ⟨St.A, l, x, m'.sym :: r'⟩) :=
        fun r'' => (ih d hd hu' hsplit.2 x l r'').1
      rcases hc with h | h <;> subst h
      · refine ⟨?_, fun _ => ?_⟩
        · obtain ⟨n, m', r', hn⟩ := key ((2 : Sym) :: r)
          refine ⟨1 + n, m', r', ?_⟩
          rw [iter_add]
          have h1 : iter 1 (some (⟨St.A, (d :: u) ++ x :: l, 3, (2 : Sym) :: r⟩ : Cfg)) =
              some ⟨St.A, u ++ x :: l, d, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
          rw [h1]; exact hn
        · obtain ⟨n, m', r', hn⟩ := key ((3 : Sym) :: r)
          refine ⟨1 + n, m', r', ?_⟩
          rw [iter_add]
          have h1 : iter 1 (some (⟨St.A, (d :: u) ++ x :: l, 3, (3 : Sym) :: r⟩ : Cfg)) =
              some ⟨St.A, u ++ x :: l, d, (2 : Sym) :: (3 : Sym) :: r⟩ := rfl
          rw [h1]; exact hn
      · refine ⟨?_, fun h => by simp at h⟩
        have hd3 : d = 3 := by
          rcases hd with h | h
          · exact h
          · exact absurd ⟨rfl, h⟩ hsplit.1
        subst hd3
        obtain ⟨n, m', r', hn⟩ := (ih 3 hd hu' hsplit.2 x l ((4 : Sym) :: r)).2 rfl
        refine ⟨3 + n, m', r', ?_⟩
        rw [iter_add]
        have h1 : iter 3 (some (⟨St.A, ((3 : Sym) :: u) ++ x :: l, 0, (2 : Sym) :: r⟩ : Cfg)) =
            some ⟨St.A, u ++ x :: l, 3, (3 : Sym) :: (4 : Sym) :: r⟩ := rfl
        rw [h1]; exact hn

theorem cantor_value : ∀ (u : List Sym), (∀ s ∈ u, s = 3 ∨ s = 0) → ∀ i : Nat,
    counterValue u / 3 ^ i % 3 ≠ 1 := by
  intro u
  induction u with
  | nil => intro _ i; simp [counterValue]
  | cons d u ih =>
      intro hu i
      have hd : d = 3 ∨ d = 0 := hu d (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u, s = 3 ∨ s = 0 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      have hdig : digitVal d = 0 ∨ digitVal d = 2 := by
        rcases hd with h | h <;> subst h <;> simp [digitVal]
      cases i with
      | zero =>
          simp only [Nat.pow_zero, Nat.div_one, counterValue_cons]
          omega
      | succ i =>
          have hkey : counterValue (d :: u) / 3 ^ (i + 1) = counterValue u / 3 ^ i := by
            rw [Nat.pow_succ, counterValue_cons, Nat.mul_comm (3 ^ i) 3,
              ← Nat.div_div_eq_div_mul]
            congr 1
            omega
          rw [hkey]
          exact ih hu' i

theorem iter_none (j : Nat) : iter j none = none := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [iter] using ih

theorem iter_isSome_of_le {c d : Cfg} {n : Nat} (h : iter n (some c) = some d) {k : Nat}
    (hk : k ≤ n) : iter k (some c) ≠ none := by
  intro hnone
  have : iter n (some c) = none := by
    rw [show n = k + (n - k) by omega, iter_add, hnone, iter_none]
  rw [h] at this
  exact Option.some_ne_none d this

theorem no_halt_of_cascade_into_four (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n : Nat, (∀ k ≤ n, iter k (some ⟨St.A, u ++ (4 : Sym) :: l, c, (2 : Sym) :: r⟩) ≠ none) ∧
      ∃ (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ (4 : Sym) :: l, c, (2 : Sym) :: r⟩) =
          some ⟨St.A, l, 4, m'.sym :: r'⟩ := by
  obtain ⟨n, m', r', hn⟩ := (cantor_traverse u c hc hu hno 4 l r).1
  exact ⟨n, fun k hk => iter_isSome_of_le hn hk, m', r', hn⟩

def Reachable (c : Cfg) : Prop := ∃ n, run n = some c

theorem Reachable.iter {c d : Cfg} (h : Reachable c) {n : Nat}
    (hn : iter n (some c) = some d) : Reachable d := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [run, iter_add, ← run, ht, hn]⟩

theorem halts_of_reachable {c : Cfg} (h : Reachable c) {n : Nat}
    (hn : iter n (some c) = none) : Halts := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [run, iter_add, ← run, ht, hn]⟩

theorem halts_of_reachable_cantor_block (c : Sym) (u l r : List Sym)
    (hreach : Reachable ⟨St.A, u ++ (1 : Sym) :: l, c, (2 : Sym) :: r⟩)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) : Halts := by
  obtain ⟨n, hn⟩ := cascade_halt_over_cantor_block c u l r hc hu hno
  exact halts_of_reachable hreach hn

theorem reachable_counter_increment (d : Sym) (ds l r' : List Sym) (r0 : Sym)
    (hreach : Reachable ⟨St.B, ds ++ l, d, r0 :: r'⟩)
    (hd : IsDigit d) (hds : ∀ s ∈ ds, IsDigit s) (hsat : ¬ Saturated (d :: ds)) :
    Reachable ⟨St.A, incr (d :: ds) ++ l, r0, r'⟩ ∧
      counterValue (incr (d :: ds)) = counterValue (d :: ds) + 1 := by
  refine ⟨hreach.iter (counter_increment d ds hd hds hsat l r' r0), ?_⟩
  refine counterValue_incr (d :: ds) ?_ hsat
  intro s hs
  rcases List.mem_cons.mp hs with h | h
  · exact h ▸ hd
  · exact hds s h

/-! ## Shield: a `4` or two consecutive `0`s stops a cascade -/

def CascadeOver (d : Cfg) : Prop :=
  (∃ l c r, d = ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r⟩) ∨
  (∃ l x r, d = ⟨St.A, (4 : Sym) :: (2 : Sym) :: l, x, r⟩) ∨
  (∃ l r, d = ⟨St.A, (3 : Sym) :: l, 2, r⟩) ∨
  (∃ l x r, d = ⟨St.A, (4 : Sym) :: (1 : Sym) :: l, x, r⟩)

theorem casc_three (a : Sym) (mo : Mode) (L r : List Sym) :
    iter 1 (some (⟨St.A, a :: L, 3, mo.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, (2 : Sym) :: mo.sym :: r⟩ := by
  cases mo <;> rfl

theorem casc_zero_P (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 0, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, Mode.Q.sym :: (4 : Sym) :: r⟩ := rfl

theorem casc_two_Q (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 2, Mode.Q.sym :: r⟩ : Cfg)) =
      some ⟨St.A, L, a, Mode.P.sym :: (2 : Sym) :: r⟩ := rfl

theorem casc_stop_two_P (L r : List Sym) :
    iter 1 (some (⟨St.A, L, 2, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.A, (3 : Sym) :: L, 2, r⟩ := rfl

theorem casc_stop_zero_Q (L rr : List Sym) :
    iter 2 (some (⟨St.A, L, 0, Mode.Q.sym :: rr⟩ : Cfg)) =
      some (onFirst St.A ((4 : Sym) :: (1 : Sym) :: L) rr) := by
  cases rr <;> rfl

theorem casc_stop_four_P (a : Sym) (L r : List Sym) :
    iter 3 (some (⟨St.A, a :: L, 4, Mode.P.sym :: r⟩ : Cfg)) =
      some ⟨St.B, L, a, (4 : Sym) :: (4 : Sym) :: r⟩ := rfl

theorem casc_stop_four_Q (L rr : List Sym) :
    iter 2 (some (⟨St.A, L, 4, Mode.Q.sym :: rr⟩ : Cfg)) =
      some (onFirst St.A ((4 : Sym) :: (2 : Sym) :: L) rr) := by
  cases rr <;> rfl

theorem cascade_hits_four (mo : Mode) (a : Sym) (L r : List Sym) :
    ∃ (N : Nat) (d : Cfg), iter N (some (⟨St.A, a :: L, 4, mo.sym :: r⟩ : Cfg)) = some d ∧
      CascadeOver d := by
  cases mo with
  | P =>
      exact ⟨3, _, casc_stop_four_P a L r, Or.inl ⟨L, a, r, rfl⟩⟩
  | Q =>
      refine ⟨2, _, casc_stop_four_Q (a :: L) r, Or.inr (Or.inl ?_)⟩
      cases r with
      | nil => exact ⟨a :: L, 0, [], rfl⟩
      | cons x r' => exact ⟨a :: L, x, r', rfl⟩

theorem sym_cases (c : Sym) (hc : c ≠ 1) : c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  cases c
  · exact Or.inl rfl
  · exact absurd rfl hc
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem casc_cross (c : Sym) (hc : c ≠ 1) (mo : Mode) (a : Sym) (L r : List Sym) :
    (∃ (N : Nat) (d : Cfg),
        iter N (some (⟨St.A, a :: L, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d) ∨
    (∃ (N : Nat) (mo' : Mode) (r' : List Sym),
        iter N (some (⟨St.A, a :: L, c, mo.sym :: r⟩ : Cfg)) =
          some (cfgAt St.A (a :: L) (mo'.sym :: r'))) := by
  rcases sym_cases c hc with h | h | h | h <;> subst h
  · cases mo with
    | P => exact Or.inr ⟨3, Mode.Q, (4 : Sym) :: r, casc_zero_P a L r⟩
    | Q =>
        refine Or.inl ⟨2, _, casc_stop_zero_Q (a :: L) r, Or.inr (Or.inr (Or.inr ?_))⟩
        cases r with
        | nil => exact ⟨a :: L, 0, [], rfl⟩
        | cons x r' => exact ⟨a :: L, x, r', rfl⟩
  · cases mo with
    | P =>
        exact Or.inl ⟨1, _, casc_stop_two_P (a :: L) r,
          Or.inr (Or.inr (Or.inl ⟨a :: L, r, rfl⟩))⟩
    | Q => exact Or.inr ⟨3, Mode.P, (2 : Sym) :: r, casc_two_Q a L r⟩
  · exact Or.inr ⟨1, Mode.P, mo.sym :: r, casc_three a mo L r⟩
  · exact Or.inl (cascade_hits_four mo a L r)

def StopsCascade (v : List Sym) : Prop :=
  ∀ (mo : Mode) (r : List Sym), ∃ (N : Nat) (d : Cfg),
    iter N (some (cfgAt St.A v (mo.sym :: r))) = some d ∧ CascadeOver d

theorem stopsCascade_four (zc : Sym) (zs : List Sym) :
    StopsCascade ((4 : Sym) :: zc :: zs) :=
  fun mo r => cascade_hits_four mo zc zs r

theorem stopsCascade_zero_zero (z : List Sym) :
    StopsCascade ((0 : Sym) :: (0 : Sym) :: z) := by
  intro mo r
  cases mo with
  | P =>
      refine ⟨3 + 2, _, ?_, Or.inr (Or.inr (Or.inr ⟨z, 4, r, rfl⟩))⟩
      rw [iter_add]
      show iter 2 (iter 3 (some (⟨St.A, (0 : Sym) :: z, 0, Mode.P.sym :: r⟩ : Cfg))) = _
      rw [casc_zero_P, casc_stop_zero_Q z ((4 : Sym) :: r)]
      rfl
  | Q =>
      refine ⟨2, _, casc_stop_zero_Q ((0 : Sym) :: z) r, Or.inr (Or.inr (Or.inr ?_))⟩
      cases r with
      | nil => exact ⟨(0 : Sym) :: z, 0, [], rfl⟩
      | cons x r' => exact ⟨(0 : Sym) :: z, x, r', rfl⟩

theorem cascade_dies_before_stopper : ∀ (u : List Sym), (∀ s ∈ u, s ≠ 1) →
    ∀ (a : Sym) (v : List Sym), StopsCascade (a :: v) →
    ∀ (c : Sym), c ≠ 1 → ∀ (mo : Mode) (r : List Sym),
    ∃ (N : Nat) (d : Cfg),
      iter N (some (⟨St.A, u ++ a :: v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  intro u
  induction u with
  | nil =>
      intro _ a v hv c hc mo r
      have hL : ([] : List Sym) ++ a :: v = a :: v := rfl
      rw [hL]
      rcases casc_cross c hc mo a v r with h | ⟨N, mo', r', hN⟩
      · exact h
      · obtain ⟨M, d, hM, hd⟩ := hv mo' r'
        exact ⟨N + M, d, by rw [iter_add, hN]; exact hM, hd⟩
  | cons b u ih =>
      intro hu a v hv c hc mo r
      have hb : b ≠ 1 := hu b (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u, s ≠ 1 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      have hsplit : (b :: u) ++ a :: v = b :: (u ++ a :: v) := rfl
      rw [hsplit]
      rcases casc_cross c hc mo b (u ++ a :: v) r with h | ⟨N, mo', r', hN⟩
      · exact h
      · obtain ⟨M, d, hM, hd⟩ := ih hu' a v hv b hb mo' r'
        exact ⟨N + M, d, by rw [iter_add, hN]; exact hM, hd⟩

theorem cascade_reaches_stop (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym) :
    ∃ (N : Nat) (d : Cfg),
      iter N (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg)) = some d ∧
        CascadeOver d :=
  cascade_dies_before_stopper u hu 4 (zc :: zs) (stopsCascade_four zc zs) c hc mo r

theorem cascade_dies_of_not_cantor (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (v : List Sym) (hv : (∃ zc zs, v = (4 : Sym) :: zc :: zs) ∨ (∃ z, v = (0 : Sym) :: 0 :: z))
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (r : List Sym) :
    ∃ (N : Nat) (d : Cfg),
      iter N (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  rcases hv with ⟨zc, zs, rfl⟩ | ⟨z, rfl⟩
  · exact cascade_dies_before_stopper u hu 4 (zc :: zs) (stopsCascade_four zc zs) c hc mo r
  · exact cascade_dies_before_stopper u hu 0 (0 :: z) (stopsCascade_zero_zero z) c hc mo r

theorem no_halt_before_stopper (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (v : List Sym) (hv : (∃ zc zs, v = (4 : Sym) :: zc :: zs) ∨ (∃ z, v = (0 : Sym) :: 0 :: z))
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (r : List Sym) :
    ∃ (N : Nat) (d : Cfg),
      (∀ k ≤ N, iter k (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) ≠ none) ∧
      iter N (some (⟨St.A, u ++ v, c, mo.sym :: r⟩ : Cfg)) = some d ∧ CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_dies_of_not_cantor u hu v hv c hc mo r
  exact ⟨N, d, fun k hk => iter_isSome_of_le hN hk, hN, hd⟩

theorem cascade_dies_before_four (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym) :
    ∃ (N : Nat) (d : Cfg),
      (∀ k ≤ N, iter k (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg))
        ≠ none) ∧
      iter N (some (⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩ : Cfg)) = some d ∧
        CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_reaches_stop u hu c hc mo zc zs r
  exact ⟨N, d, fun k hk => iter_isSome_of_le hN hk, hN, hd⟩

/-- Sharpened shield: the stopping `4` has at least one cell to its left.
This is the form that matches `cascade_dies_before_four` after the `A3` step
without a separate left-edge case. -/
def ShieldBeforeOneDeep (l : List Sym) : Prop :=
  ∃ (u : List Sym) (zc : Sym) (zs : List Sym),
    l = u ++ (4 : Sym) :: zc :: zs ∧ ∀ s ∈ u, s ≠ 1

def A3ShieldDeep : Prop :=
  ∀ c : Cfg, Reachable c → c.st = St.A → c.cur = 3 → ShieldBeforeOneDeep c.left

/-- The observed margin-1 boundary shape at an `A`-on-`3`: the nearest `4`
has a `1` immediately beyond it, and no `1` lies between the head and that
`4`. -/
def A3MarginOne (l : List Sym) : Prop :=
  ∃ (u zs : List Sym), l = u ++ (4 : Sym) :: (1 : Sym) :: zs ∧ ∀ s ∈ u, s ≠ 1

theorem a3MarginOne_deep {l : List Sym} (h : A3MarginOne l) :
    ShieldBeforeOneDeep l := by
  rcases h with ⟨u, zs, hl, hu⟩
  subst l
  exact ⟨u, 1, zs, rfl, hu⟩

/-- Prepending any non-`1` cell preserves the deep shield.  This is the local
preservation step used while a cascade moves toward the stopping `4`. -/
theorem shieldDeep_cons {a : Sym} (ha : a ≠ 1) {l : List Sym}
    (h : ShieldBeforeOneDeep l) : ShieldBeforeOneDeep (a :: l) := by
  rcases h with ⟨u, zc, zs, hl, hu⟩
  subst l
  refine ⟨a :: u, zc, zs, rfl, ?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ha
  · exact hu s hs

/-- The margin-1 shape is a special case of the deep shield, stable under
prepending non-`1` cells. -/
theorem a3MarginOne_prefix {a : Sym} (ha : a ≠ 1) {l : List Sym}
    (h : A3MarginOne l) : A3MarginOne (a :: l) := by
  rcases h with ⟨u, zs, hl, hu⟩
  subst l
  refine ⟨a :: u, zs, rfl, ?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ha
  · exact hu s hs

theorem cascade_from_A3_deep {c : Cfg} (hA : c.st = St.A) (h3 : c.cur = 3)
    (h : ShieldBeforeOneDeep c.left) :
    ∃ (N : Nat) (d : Cfg),
      (∀ k ≤ N, iter k (some c) ≠ none) ∧
      iter N (some c) = some d ∧ CascadeOver d := by
  rcases c with ⟨st, left, cur, right⟩
  change st = St.A at hA
  subst st
  change cur = 3 at h3
  subst cur
  obtain ⟨u, zc, zs, hleft, hu⟩ := h
  change left = u ++ (4 : Sym) :: zc :: zs at hleft
  subst left
  cases u with
  | nil =>
      obtain ⟨N, d, hN, hd⟩ := cascade_hits_four Mode.P zc zs right
      have hstep : iter 1 (some (⟨St.A, (4 : Sym) :: zc :: zs, 3, right⟩ : Cfg)) =
          some ⟨St.A, zc :: zs, 4, (2 : Sym) :: right⟩ := rfl
      have hN' : iter (1 + N) (some (⟨St.A, (4 : Sym) :: zc :: zs, 3, right⟩ : Cfg)) = some d := by
        rw [iter_add, hstep]
        exact hN
      exact ⟨1 + N, d, fun k hk => iter_isSome_of_le hN' hk, hN', hd⟩
  | cons a u' =>
      have ha : a ≠ 1 := hu a (List.mem_cons_self ..)
      have hu' : ∀ s ∈ u', s ≠ 1 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
      obtain ⟨N, d, _, hN, hd⟩ :=
        cascade_dies_before_four u' hu' a ha Mode.P zc zs right
      have hstep : iter 1 (some (⟨St.A, a :: (u' ++ (4 : Sym) :: zc :: zs), 3, right⟩ : Cfg)) =
          some ⟨St.A, u' ++ (4 : Sym) :: zc :: zs, a, (2 : Sym) :: right⟩ := rfl
      have hN' : iter (1 + N) (some (⟨St.A, a :: (u' ++ (4 : Sym) :: zc :: zs), 3, right⟩ : Cfg)) = some d := by
        rw [iter_add, hstep]
        exact hN
      exact ⟨1 + N, d, fun k hk => iter_isSome_of_le hN' hk, hN', hd⟩

theorem a3_deep_cascade {c : Cfg} (hr : Reachable c) (hA : c.st = St.A)
    (h3 : c.cur = 3) (h : A3ShieldDeep) :
    ∃ d, Reachable d ∧ CascadeOver d := by
  obtain ⟨N, d, _, hN, hd⟩ := cascade_from_A3_deep hA h3 (h c hr hA h3)
  exact ⟨d, hr.iter hN, hd⟩

theorem a3_margin_one_cascade {c : Cfg} (hA : c.st = St.A) (h3 : c.cur = 3)
    (h : A3MarginOne c.left) :
    ∃ (N : Nat) (d : Cfg),
      (∀ k ≤ N, iter k (some c) ≠ none) ∧
      iter N (some c) = some d ∧ CascadeOver d :=
  cascade_from_A3_deep hA h3 (a3MarginOne_deep h)

theorem reachable_cascade_over (u : List Sym) (hu : ∀ s ∈ u, s ≠ 1)
    (c : Sym) (hc : c ≠ 1) (mo : Mode) (zc : Sym) (zs r : List Sym)
    (hreach : Reachable ⟨St.A, u ++ (4 : Sym) :: zc :: zs, c, mo.sym :: r⟩) :
    ∃ d, Reachable d ∧ CascadeOver d := by
  obtain ⟨N, d, hN, hd⟩ := cascade_reaches_stop u hu c hc mo zc zs r
  exact ⟨d, hreach.iter hN, hd⟩


/-! ## Halting criterion and the pre-halt left arrival -/

/-- Every halting time has an earlier configuration whose next step halts.  This
is proved by induction, avoiding `Nat.find`. -/
theorem halt_has_predecessor : ∀ n : Nat, run n = none →
    ∃ m : Nat, m < n ∧ ∃ c : Cfg, run m = some c ∧ step c = none := by
  intro n
  induction n with
  | zero => intro h; simp [run_zero] at h
  | succ n ih =>
      intro h
      rw [run_succ] at h
      cases hr : run n with
      | none =>
          obtain ⟨m, hmn, c, hmc, hstep⟩ := ih hr
          exact ⟨m, Nat.lt_succ_of_lt hmn, c, hmc, hstep⟩
      | some c =>
          rw [hr] at h
          have hstep : step c = none := by simpa [ostep] using h
          exact ⟨n, Nat.lt_succ_self n, c, hr, hstep⟩

/-- **Halting criterion.**  The machine halts iff it ever is in state `A`
scanning the symbol `1`; this is the only undefined transition. -/
theorem halts_iff_state_A_reads_one :
    Halts ↔ ∃ (n : Nat) (c : Cfg), run n = some c ∧ c.st = St.A ∧ c.cur = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hmn, c, hc, hstep⟩ := halt_has_predecessor n hn
    exact ⟨m, c, hc, (step_eq_none_iff c).mp hstep⟩
  · rintro ⟨n, c, hc, h1, h2⟩
    refine ⟨n + 1, ?_⟩
    rw [run_succ, hc]
    simpa [ostep] using (step_eq_none_iff c).mpr ⟨h1, h2⟩

/-- **How a halt can be reached.**  If a step leads to state `A` on a `1`, the
head was adjacent to that `1` before the step, in one of exactly five local
situations. -/
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

/-- **A halt is always a left-arrival on a `1`.**  Using `NoOneRight`, the three
right-moving cases of `pre_halt_shape` are impossible, leaving only `A` on `3`
or `B` on `1`, with a `1` immediately to the left. -/
theorem halt_needs_left_arrival (h : Halts) :
    ∃ (c : Cfg) (l : List Sym), Reachable c ∧ c.left = 1 :: l ∧
      ((c.st = St.A ∧ c.cur = 3) ∨ (c.st = St.B ∧ c.cur = 1)) := by
  obtain ⟨n, d, hd, hA, h1⟩ := halts_iff_state_A_reads_one.mp h
  cases n with
  | zero =>
      rw [run_zero] at hd
      cases hd
      exact absurd h1 (by decide)
  | succ m =>
      rw [run_succ] at hd
      cases hr : run m with
      | none => rw [hr] at hd; simp at hd
      | some c =>
          rw [hr] at hd
          have hstep : step c = some d := hd
          have hno : NoOneRight c := noOneRight_run m c hr
          rcases pre_halt_shape c d hstep hA h1 with
            ⟨hs, hc, l, hl⟩ | ⟨hs, hc, l, hl⟩ | ⟨_, _, r, hr'⟩ | ⟨_, _, r, hr'⟩ | ⟨_, _, r, hr'⟩
          · exact ⟨c, l, ⟨m, hr⟩, hl, Or.inl ⟨hs, hc⟩⟩
          · exact ⟨c, l, ⟨m, hr⟩, hl, Or.inr ⟨hs, hc⟩⟩
          · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno
          · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno
          · exact absurd (show (1 : Sym) ∈ c.right by rw [hr']; exact List.mem_cons_self ..) hno

/-! ## The observed four-shield invariant -/

/-- From the head outwards, the left tape has a `4` before any `1`.  This is
exactly the shape that makes `cascade_dies_before_four` applicable to an `A`
cascade born on a `3`. -/
def ShieldBeforeOne (l : List Sym) : Prop :=
  ∃ u v : List Sym, l = u ++ (4 : Sym) :: v ∧ ∀ s ∈ u, s ≠ 1

/-- Boolean scan for `ShieldBeforeOne`. -/
def shieldB : List Sym → Bool
  | [] => false
  | Sym.s1 :: _ => false
  | Sym.s4 :: _ => true
  | _ :: xs => shieldB xs

/-- Soundness of the Boolean scan. -/
theorem shieldB_sound : ∀ l : List Sym, shieldB l = true → ShieldBeforeOne l
  | [], h => by simp [shieldB] at h
  | Sym.s1 :: xs, h => by simp [shieldB] at h
  | Sym.s4 :: xs, _ => ⟨[], xs, rfl, by simp⟩
  | Sym.s0 :: xs, h => by
      have h' : shieldB xs = true := by simpa [shieldB] using h
      obtain ⟨u, v, huv, hu⟩ := shieldB_sound xs h'
      refine ⟨Sym.s0 :: u, v, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'
  | Sym.s2 :: xs, h => by
      have h' : shieldB xs = true := by simpa [shieldB] using h
      obtain ⟨u, v, huv, hu⟩ := shieldB_sound xs h'
      refine ⟨Sym.s2 :: u, v, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'
  | Sym.s3 :: xs, h => by
      have h' : shieldB xs = true := by simpa [shieldB] using h
      obtain ⟨u, v, huv, hu⟩ := shieldB_sound xs h'
      refine ⟨Sym.s3 :: u, v, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'

/-- Boolean scan for the sharpened shield. -/
def shieldDeepB : List Sym → Bool
  | [] => false
  | _ :: [] => false
  | Sym.s1 :: _ :: _ => false
  | Sym.s4 :: _ :: _ => true
  | _ :: y :: xs => shieldDeepB (y :: xs)

theorem shieldDeepB_sound : ∀ l : List Sym, shieldDeepB l = true → ShieldBeforeOneDeep l
  | [], h => by simp [shieldDeepB] at h
  | _ :: [], h => by simp [shieldDeepB] at h
  | Sym.s1 :: _ :: _, h => by simp [shieldDeepB] at h
  | Sym.s4 :: y :: xs, _ => ⟨[], y, xs, rfl, by simp⟩
  | Sym.s0 :: y :: xs, h => by
      have h' : shieldDeepB (y :: xs) = true := by simpa [shieldDeepB] using h
      obtain ⟨u, zc, zs, huv, hu⟩ := shieldDeepB_sound (y :: xs) h'
      refine ⟨Sym.s0 :: u, zc, zs, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'
  | Sym.s2 :: y :: xs, h => by
      have h' : shieldDeepB (y :: xs) = true := by simpa [shieldDeepB] using h
      obtain ⟨u, zc, zs, huv, hu⟩ := shieldDeepB_sound (y :: xs) h'
      refine ⟨Sym.s2 :: u, zc, zs, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'
  | Sym.s3 :: y :: xs, h => by
      have h' : shieldDeepB (y :: xs) = true := by simpa [shieldDeepB] using h
      obtain ⟨u, zc, zs, huv, hu⟩ := shieldDeepB_sound (y :: xs) h'
      refine ⟨Sym.s3 :: u, zc, zs, by simp [huv], ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · decide
      · exact hu s hs'

/-- Boolean check that `B` on a `1` never has a `1` immediately to its left. -/
def noOneLeftB : List Sym → Bool
  | [] => true
  | Sym.s1 :: _ => false
  | _ :: _ => true

theorem noOneLeftB_sound (l : List Sym) (h : noOneLeftB l = true) :
    ∀ u : List Sym, l ≠ (1 : Sym) :: u := by
  intro u hu
  cases l with
  | nil => simp at hu
  | cons x xs => cases x <;> simp [noOneLeftB] at h hu

/-- The two invariants observed at every `A`-on-`3` birth and every `B`-on-`1`
configuration. -/
def A3Shield : Prop :=
  ∀ c : Cfg, Reachable c → c.st = St.A → c.cur = 3 → ShieldBeforeOne c.left

theorem A3Shield_of_deep (h : A3ShieldDeep) : A3Shield := by
  intro c hr hA h3
  obtain ⟨u, zc, zs, he, hu⟩ := h c hr hA h3
  exact ⟨u, zc :: zs, he, hu⟩

def B1Safe : Prop :=
  ∀ c : Cfg, Reachable c → c.st = St.B → c.cur = 1 →
    ∀ l : List Sym, c.left ≠ (1 : Sym) :: l

/-- A single pass checking both Boolean invariants. -/
def okAt (c : Cfg) : Bool :=
  (if c.st = St.A ∧ c.cur = 3 then shieldB c.left else true) &&
  (if c.st = St.B ∧ c.cur = 1 then noOneLeftB c.left else true)

theorem okAt_sound (c : Cfg) (h : okAt c = true) :
    (c.st = St.A → c.cur = 3 → ShieldBeforeOne c.left) ∧
    (c.st = St.B → c.cur = 1 → ∀ l : List Sym, c.left ≠ (1 : Sym) :: l) := by
  simp only [okAt, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hA h3
    have hb : shieldB c.left = true := by simpa [hA, h3] using h1
    exact shieldB_sound c.left hb
  · intro hB h1'
    have hb : noOneLeftB c.left = true := by simpa [hB, h1'] using h2
    exact noOneLeftB_sound c.left hb

def okAtDeep (c : Cfg) : Bool :=
  (if c.st = St.A ∧ c.cur = 3 then shieldDeepB c.left else true) &&
  (if c.st = St.B ∧ c.cur = 1 then noOneLeftB c.left else true)

theorem okAtDeep_sound (c : Cfg) (h : okAtDeep c = true) :
    (c.st = St.A → c.cur = 3 → ShieldBeforeOneDeep c.left) ∧
    (c.st = St.B → c.cur = 1 → ∀ l : List Sym, c.left ≠ (1 : Sym) :: l) := by
  simp only [okAtDeep, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hA h3
    have hb : shieldDeepB c.left = true := by simpa [hA, h3] using h1
    exact shieldDeepB_sound c.left hb
  · intro hB h1'
    have hb : noOneLeftB c.left = true := by simpa [hB, h1'] using h2
    exact noOneLeftB_sound c.left hb

def checkInvariants : Nat → Option Cfg → Bool
  | 0, _ => true
  | _n + 1, none => false
  | n + 1, some c => okAt c && checkInvariants n (step c)

theorem checkInvariants_sound (n : Nat) (o : Option Cfg)
    (h : checkInvariants n o = true) :
    ∀ k : Nat, k < n → ∀ c : Cfg, iter k o = some c →
      ((c.st = St.A → c.cur = 3 → ShieldBeforeOne c.left) ∧
       (c.st = St.B → c.cur = 1 → ∀ l : List Sym, c.left ≠ (1 : Sym) :: l)) := by
  induction n generalizing o with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk c hc
      cases o with
      | none => simp [checkInvariants] at h
      | some c0 =>
          simp only [checkInvariants, Bool.and_eq_true] at h
          obtain ⟨hhead, htail⟩ := h
          cases k with
          | zero =>
              have hc0 : c0 = c := by simpa [iter] using hc
              subst c
              exact okAt_sound c0 hhead
          | succ k =>
              exact ih (step c0) htail k (by omega) c (by simpa [iter, ostep] using hc)

def checkInvariantsDeep : Nat → Option Cfg → Bool
  | 0, _ => true
  | _n + 1, none => false
  | n + 1, some c => okAtDeep c && checkInvariantsDeep n (step c)

theorem checkInvariantsDeep_sound (n : Nat) (o : Option Cfg)
    (h : checkInvariantsDeep n o = true) :
    ∀ k : Nat, k < n → ∀ c : Cfg, iter k o = some c →
      ((c.st = St.A → c.cur = 3 → ShieldBeforeOneDeep c.left) ∧
       (c.st = St.B → c.cur = 1 → ∀ l : List Sym, c.left ≠ (1 : Sym) :: l)) := by
  induction n generalizing o with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk c hc
      cases o with
      | none => simp [checkInvariantsDeep] at h
      | some c0 =>
          simp only [checkInvariantsDeep, Bool.and_eq_true] at h
          obtain ⟨hhead, htail⟩ := h
          cases k with
          | zero =>
              have hc0 : c0 = c := by simpa [iter] using hc
              subst c
              exact okAtDeep_sound c0 hhead
          | succ k =>
              exact ih (step c0) htail k (by omega) c (by simpa [iter, ostep] using hc)

/-- Compiled finite certificate: both invariants hold through step `10^8`.
This is a finite check, not the global invariant. -/
theorem invariants_checked_to_hundred_million :
    checkInvariants 100000001 (some init) = true := by
  native_decide

theorem invariantsDeep_checked_to_million :
    checkInvariantsDeep 1000001 (some init) = true := by
  native_decide

theorem a3_deep_before_million {n : Nat} (hn : n ≤ 1000000)
    {c : Cfg} (hc : run n = some c) (hA : c.st = St.A) (h3 : c.cur = 3) :
    ShieldBeforeOneDeep c.left := by
  have h := checkInvariantsDeep_sound 1000001 (some init)
    invariantsDeep_checked_to_million n (by omega) c (by simpa [run] using hc)
  exact h.1 hA h3

theorem a3_shield_before_hundred_million {n : Nat} (hn : n ≤ 100000000)
    {c : Cfg} (hc : run n = some c) (hA : c.st = St.A) (h3 : c.cur = 3) :
    ShieldBeforeOne c.left := by
  have h := checkInvariants_sound 100000001 (some init)
    invariants_checked_to_hundred_million n (by omega) c (by simpa [run] using hc)
  exact h.1 hA h3

theorem b1_safe_before_hundred_million {n : Nat} (hn : n ≤ 100000000)
    {c : Cfg} (hc : run n = some c) (hB : c.st = St.B) (h1 : c.cur = 1) :
    ∀ l : List Sym, c.left ≠ (1 : Sym) :: l := by
  have h := checkInvariants_sound 100000001 (some init)
    invariants_checked_to_hundred_million n (by omega) c (by simpa [run] using hc)
  exact h.2 hB h1

/-- A shield cannot start with the frontier symbol. -/
theorem not_shieldBeforeOne_cons_one (l : List Sym) :
    ¬ ShieldBeforeOne ((1 : Sym) :: l) := by
  rintro ⟨u, v, huv, hu⟩
  cases u with
  | nil => simp at huv
  | cons a u' =>
      have ha : a = (1 : Sym) := by
        injection huv with h _
        exact h.symm
      exact (hu (1 : Sym) (by rw [← ha]; exact List.mem_cons_self ..)) rfl

/-- **Conditional nonhalting theorem.**  If the observed `A3` shield and `B1`
safety invariants were global, the machine would not halt.  Both hypotheses are
left open here; this is a reduction, not an unconditional proof. -/
theorem not_halts_of_A3Shield_B1Safe (hA3 : A3Shield) (hB1 : B1Safe) : ¬ Halts := by
  intro hh
  obtain ⟨c, l, hreach, hl, hcase⟩ := halt_needs_left_arrival hh
  rcases hcase with ⟨hst, hcur⟩ | ⟨hst, hcur⟩
  · have hs : ShieldBeforeOne c.left := hA3 c hreach hst hcur
    rw [hl] at hs
    exact not_shieldBeforeOne_cons_one l hs
  · exact hB1 c hreach hst hcur l hl

theorem not_halts_of_A3ShieldDeep_B1Safe (hA3 : A3ShieldDeep) (hB1 : B1Safe) : ¬ Halts :=
  not_halts_of_A3Shield_B1Safe (A3Shield_of_deep hA3) hB1

end TM25
#print axioms TM25.step_eq_none_iff
#print axioms TM25.noOneRight_run
#print axioms TM25.not_halted_before_hundred_million
#print axioms TM25.counter_increment
#print axioms TM25.counter_overflow
#print axioms TM25.cross_digits_iff
#print axioms TM25.cascade_dies_of_not_cantor
#print axioms TM25.halts_of_reachable_cantor_block
#print axioms TM25.halt_needs_left_arrival
#print axioms TM25.shieldB_sound
#print axioms TM25.invariants_checked_to_hundred_million
#print axioms TM25.not_halts_of_A3Shield_B1Safe
#print axioms TM25.shieldDeepB_sound
#print axioms TM25.invariantsDeep_checked_to_million
#print axioms TM25.a3_deep_before_million
#print axioms TM25.cascade_from_A3_deep
#print axioms TM25.a3_deep_cascade
#print axioms TM25.not_halts_of_A3ShieldDeep_B1Safe
#print axioms TM25.a3_margin_one_cascade
#print axioms TM25.shieldDeep_cons
