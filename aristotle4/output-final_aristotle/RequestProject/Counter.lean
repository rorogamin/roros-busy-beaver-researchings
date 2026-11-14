import RequestProject.Machine

/-!
# Counter dynamics of `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`

This file develops, and machine-checks, the two ingredients that were only
described informally in `ANALYSIS.md`:

* **the base-3 counter** formed by the cells to the right of the leftmost `1`
  (the *frontier*), together with the exact macroscopic rule by which a visit
  of the head coming from the right increments it (§ "Counter");
* **the cascade calculus**: the left-moving `A`-signal is a two-mode particle
  (`P`/`Q`), and the set of tape words it can cross is a regular language.
  Reading the crossed cells as base-3 digits (`3 ↦ 0`, `4 ↦ 1`, `0 ↦ 2`), the
  crossable blocks are exactly the words whose digits avoid `1` and never have
  two consecutive `2`s, i.e. *Cantor-set* values in base 3 subject to an extra
  non-adjacency condition.  This makes precise — and corrects — the
  "Cantor value" criterion of `ANALYSIS.md` §2.4.

Everything here is a theorem about *arbitrary* configurations of the machine:
each statement is of the form "if the machine is ever in a configuration of
such and such shape, then ...".  The (still open) global question is whether
the configurations actually reached from the blank tape have the shapes
described here; see `ANALYSIS.md`.
-/

namespace TM2x5

/-! ## Digits and counter values

A counter cell carries a base-3 digit under the encoding

| symbol | `3` | `4` | `0` |
|---|---|---|---|
| digit  | 0   | 1   | 2   |

Counter words are always written **least significant digit first**, which is
the order in which the head (arriving from the right) meets them. -/

/-- The digit carried by a counter cell (`2`, the "pending reset" symbol, and
`1`, the frontier marker, are not digits and are given the value `0`). -/
def digitVal : Sym → ℕ
  | Sym.s3 => 0
  | Sym.s4 => 1
  | Sym.s0 => 2
  | _ => 0

/-- A cell is a counter digit iff it is one of `3`, `4`, `0`. -/
def IsDigit (s : Sym) : Prop := s = 3 ∨ s = 4 ∨ s = 0

/-- The value of a counter word, least significant digit first. -/
def counterValue : List Sym → ℕ
  | [] => 0
  | d :: ds => digitVal d + 3 * counterValue ds

@[simp] theorem counterValue_nil : counterValue [] = 0 := rfl

@[simp] theorem counterValue_cons (d : Sym) (ds : List Sym) :
    counterValue (d :: ds) = digitVal d + 3 * counterValue ds := rfl

/-- Increment of a counter word (least significant digit first).  A digit `2`
(symbol `0`) is reset to `0` (symbol `3`) and the carry propagates. -/
def incr : List Sym → List Sym
  | [] => []
  | Sym.s3 :: ds => (4 : Sym) :: ds
  | Sym.s4 :: ds => (0 : Sym) :: ds
  | Sym.s0 :: ds => (3 : Sym) :: incr ds
  | d :: ds => d :: ds

/-- A counter word is *saturated* when every digit is `2` (symbol `0`); this is
exactly the situation in which an increment overflows into the frontier. -/
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

/-! ## The counter increment

The head arrives at the least significant digit from the right in state `B`.
`B3 → 4RA` and `B4 → 0RA` increment the digit and turn the head around;
`B0 → 2LB` resets the digit to the *pending* symbol `2` and carries.  On the
way back out, `A2 → 3RA` rewrites every pending `2` as the digit `0` (symbol
`3`).  The cost of the whole operation: -/
def incrCost : List Sym → ℕ
  | Sym.s3 :: _ => 1
  | Sym.s4 :: _ => 1
  | Sym.s0 :: ds => incrCost ds + 2
  | _ => 0

/-- **The counter increment rule.**  If the head arrives in state `B` on the
least significant digit `d` of a counter word `d :: ds` that is not saturated,
then after `incrCost (d :: ds)` steps the counter word has been replaced by its
increment and the head has left the counter to the right, in state `A`. -/
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
    · -- carry: one step left, recurse, one step back out over the pending `2`
      have he : IsDigit e := hds e (List.mem_cons_self ..)
      have hes : ∀ s ∈ ds, IsDigit s := fun s hsm => hds s (List.mem_cons_of_mem _ hsm)
      have hs' : ¬ Saturated (e :: ds) := fun hsat => hs ⟨rfl, hsat⟩
      have h1 : iter 1 (some (⟨St.B, (e :: ds) ++ l, 0, r0 :: r'⟩ : Cfg))
          = some ⟨St.B, ds ++ l, e, (2 : Sym) :: r0 :: r'⟩ := rfl
      have hcost : incrCost ((0 : Sym) :: e :: ds) = 1 + (incrCost (e :: ds) + 1) := by
        simp [incrCost]
        omega
      rw [hcost, iter_add, h1, iter_add, ih e he hes hs' l (r0 :: r') 2]
      have h2 : iter 1 (some (⟨St.A, incr (e :: ds) ++ l, 2, r0 :: r'⟩ : Cfg))
          = some ⟨St.A, (3 : Sym) :: (incr (e :: ds) ++ l), r0, r'⟩ := rfl
      rw [h2]
      simp [incr]

/-- The carry of a saturated counter reaches the frontier `1`, turns it into a
`3` and steps onto the fresh blank cell to its left. -/
theorem frontier_overflow_blank (k : ℕ) (r : List Sym) :
    iter (k + 2) (some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, r⟩) =
      some ⟨St.A, [], 0, (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ r⟩ := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show (k + 1 + 2) = 1 + (k + 2) by omega, iter_add]
    have h1 : iter 1
        (some (⟨St.B, List.replicate (k + 1) (0 : Sym) ++ [1], 0, r⟩ : Cfg))
        = some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, (2 : Sym) :: r⟩ := rfl
    rw [h1, ih]
    simp [List.replicate_succ']

/-- **Overflow.**  When the counter is saturated (`k+1` digits equal to `2`),
the carry runs into the frontier `1`: the frontier is consumed, a new frontier
`1` is written one cell further left, the old frontier cell becomes the new
most significant digit `1` (symbol `4`), and all the lower digits are reset to
`0` (symbol `3`).  In other words the counter value `3^(k+1) - 1` becomes
`3^(k+1)`, with one digit more. -/
theorem counter_overflow (k : ℕ) (r0 : Sym) (r' : List Sym) :
    iter (2 * k + 5) (some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, r0 :: r'⟩) =
      some ⟨St.A, List.replicate (k + 1) (3 : Sym) ++ [(4 : Sym), (1 : Sym)], r0, r'⟩ := by
  have hsplit : 2 * k + 5 = (k + 2) + (2 + (k + 1)) := by omega
  rw [hsplit, iter_add, frontier_overflow_blank k (r0 :: r')]
  rw [iter_add]
  have h2 : iter 2 (some (⟨St.A, [], 0,
      (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ r0 :: r'⟩ : Cfg))
      = some ⟨St.A, [(4 : Sym), (1 : Sym)], 2, List.replicate k (2 : Sym) ++ r0 :: r'⟩ := by
    rw [List.replicate_succ]
    rfl
  rw [h2, A_over_twos k r0 [(4 : Sym), (1 : Sym)] r']

/-- The saturated counter with `k` digits holds the value `3 ^ k - 1`. -/
theorem counterValue_saturated (k : ℕ) :
    counterValue (List.replicate k (0 : Sym)) = 3 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [List.replicate_succ, counterValue_cons, ih]
    show 2 + 3 * (3 ^ k - 1) = 3 ^ (k + 1) - 1
    rw [pow_succ]
    omega

/-- After the overflow the counter holds `3 ^ (k+1)`, one more than the
saturated value `3 ^ (k+1) - 1` it held before: the counter has simply gained
a digit and kept counting. -/
theorem counterValue_after_overflow (k : ℕ) :
    counterValue (List.replicate (k + 1) (3 : Sym) ++ [(4 : Sym)]) = 3 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, counterValue_cons, ih]
    show 0 + 3 * 3 ^ (k + 1) = 3 ^ (k + 1 + 1)
    rw [pow_succ]
    omega

/-! ## The cascade calculus

The left-moving `A`-signal ("cascade") is a particle with two internal modes,
determined by the symbol in the cell immediately to its right:

* mode **P**: that cell contains `2`;
* mode **Q**: that cell contains `3`.

Its transition rules (all proved below) are

| mode | cell `3` | cell `0` | cell `2` | cell `4` | cell `1` |
|---|---|---|---|---|---|
| P | continue in P | continue in Q | stop | stop | **halt** |
| Q | continue in P | stop | continue in P | stop | **halt** |
-/

/-- The two modes of a left-moving cascade. -/
inductive Mode
  | P
  | Q
  deriving DecidableEq, Repr

/-- The symbol sitting to the right of the head in each mode. -/
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

/-- A cascade reading `1` halts: this is the only undefined transition. -/
theorem cascade_halts_on_one (l r : List Sym) :
    iter 1 (some ⟨St.A, l, 1, r⟩) = none := rfl

/-- In mode `P` a `4` stops the cascade, which turns into a left-moving `B`. -/
theorem cascade_P_four_stops (c : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, c :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r⟩ := rfl

/-- In mode `P` a `2` stops the cascade, which turns into a right-moving `A`. -/
theorem cascade_P_two_stops (l r : List Sym) :
    iter 1 (some ⟨St.A, l, 2, (2 : Sym) :: r⟩) =
      some ⟨St.A, (3 : Sym) :: l, 2, r⟩ := rfl

/-- In mode `Q` a `0` stops the cascade: it leaves a stray `1` behind and the
head turns right. -/
theorem cascade_Q_zero_stops (l r : List Sym) (x : Sym) :
    iter 2 (some ⟨St.A, l, 0, (3 : Sym) :: x :: r⟩) =
      some ⟨St.A, (4 : Sym) :: (1 : Sym) :: l, x, r⟩ := rfl

/-- In mode `Q` a `4` stops the cascade. -/
theorem cascade_Q_four_stops (l r : List Sym) (x : Sym) :
    iter 2 (some ⟨St.A, l, 4, (3 : Sym) :: x :: r⟩) =
      some ⟨St.A, (4 : Sym) :: (2 : Sym) :: l, x, r⟩ := rfl

/-- `Cross m c w` means: a cascade in mode `m`, currently reading the cell `c`
and with the cells `w` to its left (nearest first), runs all the way into a
frontier `1` — and therefore makes the machine halt. -/
inductive Cross : Mode → Sym → List Sym → Prop
  | haltP {w : List Sym} : Cross Mode.P 1 w
  | haltQ {w : List Sym} : Cross Mode.Q 1 w
  | P3 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.P 3 (c :: w)
  | P0 {c : Sym} {w : List Sym} : Cross Mode.Q c w → Cross Mode.P 0 (c :: w)
  | Q3 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.Q 3 (c :: w)
  | Q2 {c : Sym} {w : List Sym} : Cross Mode.P c w → Cross Mode.Q 2 (c :: w)

/-- **Crossing means halting.**  If the cells to the left of a cascade form a
crossable word, the machine halts. -/
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
    have h1 : iter 1 (some (⟨St.A, (c :: w) ++ l, 3, Mode.P.sym :: r⟩ : Cfg))
        = some ⟨St.A, w ++ l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
    rw [h1]
    exact hn
  | @P0 c w _ ih =>
    intro l r
    obtain ⟨n, hn⟩ := ih l ((4 : Sym) :: r)
    refine ⟨3 + n, ?_⟩
    rw [iter_add]
    have h1 : iter 3 (some (⟨St.A, (c :: w) ++ l, 0, Mode.P.sym :: r⟩ : Cfg))
        = some ⟨St.A, w ++ l, c, (3 : Sym) :: (4 : Sym) :: r⟩ := rfl
    rw [h1]
    exact hn
  | @Q3 c w _ ih =>
    intro l r
    obtain ⟨n, hn⟩ := ih l ((3 : Sym) :: r)
    refine ⟨1 + n, ?_⟩
    rw [iter_add]
    have h1 : iter 1 (some (⟨St.A, (c :: w) ++ l, 3, Mode.Q.sym :: r⟩ : Cfg))
        = some ⟨St.A, w ++ l, c, (2 : Sym) :: (3 : Sym) :: r⟩ := rfl
    rw [h1]
    exact hn
  | @Q2 c w _ ih =>
    intro l r
    obtain ⟨n, hn⟩ := ih l ((2 : Sym) :: r)
    refine ⟨3 + n, ?_⟩
    rw [iter_add]
    have h1 : iter 3 (some (⟨St.A, (c :: w) ++ l, 2, Mode.Q.sym :: r⟩ : Cfg))
        = some ⟨St.A, w ++ l, c, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
    rw [h1]
    exact hn

/-! ## The Cantor criterion -/

/-- The blocks a cascade in mode `P` can cross, written as words over the two
"safe" digits `3` (digit `0`) and `0` (digit `2`): no two consecutive `0`s. -/
def NoAdjacentZeros (u : List Sym) : Prop :=
  List.IsChain (fun a b => ¬ (a = (0 : Sym) ∧ b = (0 : Sym))) u

theorem cantor_cross_aux : ∀ (u : List Sym) (c : Sym), (c = 3 ∨ c = 0) →
    (∀ s ∈ u, s = 3 ∨ s = 0) → NoAdjacentZeros (c :: u) →
    Cross Mode.P c (u ++ [1]) ∧ (c = 3 → Cross Mode.Q c (u ++ [1])) := by
  intro u
  induction u with
  | nil =>
    intro c hc _ _
    rcases hc with h | h <;> subst h
    · exact ⟨Cross.P3 Cross.haltP, fun _ => Cross.Q3 Cross.haltP⟩
    · exact ⟨Cross.P0 Cross.haltQ, fun h => by simp [OfNat.ofNat] at h⟩
  | cons d u ih =>
    intro c hc hu hno
    have hd : d = 3 ∨ d = 0 := hu d (List.mem_cons_self ..)
    have hu' : ∀ s ∈ u, s = 3 ∨ s = 0 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
    have hsplit := (List.isChain_cons_cons).mp hno
    have hIH := ih d hd hu' hsplit.2
    rcases hc with h | h <;> subst h
    · exact ⟨Cross.P3 hIH.1, fun _ => Cross.Q3 hIH.1⟩
    · have hd3 : d = 3 := by
        rcases hd with h | h
        · exact h
        · exact absurd ⟨rfl, h⟩ hsplit.1
      exact ⟨Cross.P0 (hIH.2 hd3), fun h => by simp [OfNat.ofNat] at h⟩

/-- A cascade in mode `P` crosses any block of digits `0` and `2` (symbols `3`
and `0`) without two consecutive digits `2`, and runs into the frontier `1`. -/
theorem cantor_cross (u : List Sym) (c : Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    Cross Mode.P c (u ++ [1]) :=
  (cantor_cross_aux u c hc hu hno).1

/-- **The Cantor halting criterion.**  If a cascade in mode `P` faces a block
`c :: u` of digits `0` and `2` (symbols `3` and `0`) with no two consecutive
digits `2`, immediately followed by the frontier `1`, then the machine halts. -/
theorem cascade_halt_over_cantor_block (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n, iter n (some ⟨St.A, u ++ (1 : Sym) :: l, c, (2 : Sym) :: r⟩) = none := by
  have h := cross_halts (cantor_cross u c hc hu hno) l r
  simpa using h

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
      | P3 _ => exact ⟨Or.inl rfl, by simp, List.isChain_singleton _⟩
      | P0 _ => exact ⟨Or.inr rfl, by simp, List.isChain_singleton _⟩
    · intro h
      cases h with
      | haltQ => exact absurd hc not_isDigit_one
      | Q3 _ => exact ⟨rfl, by simp, List.isChain_singleton _⟩
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
        · exact List.isChain_cons_cons.mpr ⟨by simp [OfNat.ofNat], hch⟩
      | P0 h' =>
        obtain ⟨hd3, hus, hch⟩ := hIH.2 h'
        refine ⟨Or.inr rfl, ?_, ?_⟩
        · intro s hs
          rcases List.mem_cons.mp hs with h | h
          · exact h ▸ Or.inl hd3
          · exact hus s h
        · refine List.isChain_cons_cons.mpr ⟨?_, hch⟩
          rintro ⟨-, h0⟩
          rw [hd3] at h0
          simp [OfNat.ofNat] at h0
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
        · exact List.isChain_cons_cons.mpr ⟨by simp [OfNat.ofNat], hch⟩
      | Q2 _ => exact absurd hc not_isDigit_two

/-- **The exact criterion.**  For a block of counter digits followed by the
frontier, a cascade in mode `P` crosses it *if and only if* every digit is `0`
or `2` (symbol `3` or `0`) and no two consecutive digits are `2`.  So the
Cantor-type condition is not merely sufficient: it is exactly the condition
under which the frontier is reached. -/
theorem cross_digits_iff (u : List Sym) (c : Sym) (hc : IsDigit c)
    (hu : ∀ s ∈ u, IsDigit s) :
    Cross Mode.P c (u ++ [1]) ↔
      ((c = 3 ∨ c = 0) ∧ (∀ s ∈ u, s = 3 ∨ s = 0) ∧ NoAdjacentZeros (c :: u)) := by
  refine ⟨(cross_digits_aux u c hc hu).1, ?_⟩
  rintro ⟨h1, h2, h3⟩
  exact cantor_cross u c h1 h2 h3

/-- `k` copies of the alternating background pair `0 2`, in the order in which
a left-moving cascade meets them. -/
def bgPairs : ℕ → List Sym
  | 0 => []
  | k + 1 => (0 : Sym) :: (2 : Sym) :: bgPairs k

/-- **The cascade crosses the background.**  Away from the counter the tape
carries the alternating pattern `… 0 2 0 2 …`; a cascade in mode `P` crosses
any number of those pairs (three steps per cell) and comes out in mode `P`
again.  This is why cascades travel so far before meeting a digit. -/
theorem cross_bg : ∀ (k : ℕ) {c : Sym} {w : List Sym}, Cross Mode.P c w →
    Cross Mode.P 0 ((2 : Sym) :: bgPairs k ++ c :: w) := by
  intro k
  induction k with
  | zero => intro c w h; exact Cross.P0 (Cross.Q2 h)
  | succ k ih =>
    intro c w h
    have := ih h
    simpa [bgPairs] using Cross.P0 (Cross.Q2 this)

/-- **Birth of a cascade.**  When the head, in state `A`, steps onto the blank
cell at the right end of the used tape, three steps turn the two cells `0 0`
into `3 2` and send a cascade off to the left, in mode `Q`. -/
theorem cascade_birth (x : Sym) (l : List Sym) :
    iter 3 (some ⟨St.A, x :: l, 0, []⟩) = some ⟨St.A, l, x, [(3 : Sym), (2 : Sym)]⟩ := rfl

/-- **End-to-end halting criterion.**  Suppose the head is in state `A` on the
blank cell at the right end of the used tape, and that every cell between it
and the frontier `1` carries a counter digit `0` or `2` (symbol `3` or `0`),
the cell just left of the head carrying the digit `0`, with no two consecutive
digits `2`.  Then the cascade born at the right end runs all the way to the
frontier and the machine halts. -/
theorem halt_of_cantor_to_right_end (u l : List Sym)
    (hu : ∀ s ∈ u, s = 3 ∨ s = 0) (hno : NoAdjacentZeros ((3 : Sym) :: u)) :
    ∃ n, iter n (some ⟨St.A, ((3 : Sym) :: u) ++ (1 : Sym) :: l, 0, []⟩) = none := by
  obtain ⟨n, hn⟩ :=
    cross_halts ((cantor_cross_aux u 3 (Or.inl rfl) hu hno).2 rfl) l [(2 : Sym)]
  refine ⟨3 + n, ?_⟩
  rw [iter_add]
  have h1 : iter 3 (some (⟨St.A, ((3 : Sym) :: u) ++ (1 : Sym) :: l, 0, []⟩ : Cfg))
      = some ⟨St.A, u ++ (1 : Sym) :: l, 3, [(3 : Sym), (2 : Sym)]⟩ := rfl
  rw [h1]
  simpa using hn

/-- **The full halting criterion.**  A cascade in mode `P` that faces `k`
background pairs `0 2`, then a block `c :: u` of counter digits `0` and `2`
with no two consecutive digits `2`, then the frontier `1`, makes the machine
halt.  Only the digit block matters: the background is always crossed. -/
theorem halt_of_bg_then_cantor (k : ℕ) (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n, iter n (some ⟨St.A, (2 : Sym) :: bgPairs k ++ c :: u ++ (1 : Sym) :: l, 0,
      (2 : Sym) :: r⟩) = none := by
  have h := cross_halts (cross_bg k (cantor_cross u c hc hu hno)) l r
  simpa using h

/-- A concrete instance of the criterion: the cascade crosses the digit block
`0 2 0 2` (cells `3 0 3 0`, reading leftwards from the head) and halts on the
frontier ten steps later. -/
example : iter 10 (some (⟨St.A, [(0 : Sym), 3, 0, 3, (1 : Sym), 2, 2], 3, [(2 : Sym)]⟩ : Cfg))
    = none := rfl

/-- Replacing one of those digits by `1` (cell `4`) saves the frontier: the
machine is still running thirty steps later. -/
example : (iter 30 (some (⟨St.A, [(0 : Sym), 3, 4, 3, (1 : Sym), 2, 2], 3, [(2 : Sym)]⟩ : Cfg))).isSome
    = true := rfl

/-- **Crossing a Cantor block.**  A cascade in mode `P` facing a block `c :: u`
of digits `0` and `2` (symbols `3` and `0`) with no two consecutive digits `2`
traverses the whole block and arrives, still as a cascade (in mode `P` or `Q`),
at the cell `x` immediately beyond it.  Whether the machine then halts is
decided by `x` alone: `x = 1` (the frontier) halts, `x = 4` stops the cascade
harmlessly. -/
theorem cantor_traverse : ∀ (u : List Sym) (c : Sym), (c = 3 ∨ c = 0) →
    (∀ s ∈ u, s = 3 ∨ s = 0) → NoAdjacentZeros (c :: u) → ∀ (x : Sym) (l r : List Sym),
    (∃ (n : ℕ) (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ x :: l, c, (2 : Sym) :: r⟩) = some ⟨St.A, l, x, m'.sym :: r'⟩) ∧
    (c = 3 → ∃ (n : ℕ) (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ x :: l, c, (3 : Sym) :: r⟩) = some ⟨St.A, l, x, m'.sym :: r'⟩) := by
  intro u
  induction u with
  | nil =>
    intro c hc _ _ x l r
    rcases hc with h | h <;> subst h
    · refine ⟨⟨1, Mode.P, (2 : Sym) :: r, rfl⟩, fun _ => ⟨1, Mode.P, (3 : Sym) :: r, rfl⟩⟩
    · exact ⟨⟨3, Mode.Q, (4 : Sym) :: r, rfl⟩, fun h => by simp [OfNat.ofNat] at h⟩
  | cons d u ih =>
    intro c hc hu hno x l r
    have hd : d = 3 ∨ d = 0 := hu d (List.mem_cons_self ..)
    have hu' : ∀ s ∈ u, s = 3 ∨ s = 0 := fun s hs => hu s (List.mem_cons_of_mem _ hs)
    have hsplit := (List.isChain_cons_cons).mp hno
    have key : ∀ (r'' : List Sym),
        (∃ (n : ℕ) (m' : Mode) (r' : List Sym),
          iter n (some (⟨St.A, u ++ x :: l, d, (2 : Sym) :: r''⟩ : Cfg))
            = some ⟨St.A, l, x, m'.sym :: r'⟩) :=
      fun r'' => (ih d hd hu' hsplit.2 x l r'').1
    rcases hc with h | h <;> subst h
    · refine ⟨?_, fun _ => ?_⟩
      · obtain ⟨n, m', r', hn⟩ := key ((2 : Sym) :: r)
        refine ⟨1 + n, m', r', ?_⟩
        rw [iter_add]
        have h1 : iter 1 (some (⟨St.A, (d :: u) ++ x :: l, 3, (2 : Sym) :: r⟩ : Cfg))
            = some ⟨St.A, u ++ x :: l, d, (2 : Sym) :: (2 : Sym) :: r⟩ := rfl
        rw [h1]; exact hn
      · obtain ⟨n, m', r', hn⟩ := key ((3 : Sym) :: r)
        refine ⟨1 + n, m', r', ?_⟩
        rw [iter_add]
        have h1 : iter 1 (some (⟨St.A, (d :: u) ++ x :: l, 3, (3 : Sym) :: r⟩ : Cfg))
            = some ⟨St.A, u ++ x :: l, d, (2 : Sym) :: (3 : Sym) :: r⟩ := rfl
        rw [h1]; exact hn
    · refine ⟨?_, fun h => by simp [OfNat.ofNat] at h⟩
      have hd3 : d = 3 := by
        rcases hd with h | h
        · exact h
        · exact absurd ⟨rfl, h⟩ hsplit.1
      subst hd3
      obtain ⟨n, m', r', hn⟩ := (ih 3 hd hu' hsplit.2 x l ((4 : Sym) :: r)).2 rfl
      refine ⟨3 + n, m', r', ?_⟩
      rw [iter_add]
      have h1 : iter 3 (some (⟨St.A, ((3 : Sym) :: u) ++ x :: l, 0, (2 : Sym) :: r⟩ : Cfg))
          = some ⟨St.A, u ++ x :: l, 3, (3 : Sym) :: (4 : Sym) :: r⟩ := rfl
      rw [h1]; exact hn

/-- The value of a crossable block is a *Cantor* integer: no base-3 digit
equals `1`. -/
theorem cantor_value : ∀ (u : List Sym), (∀ s ∈ u, s = 3 ∨ s = 0) → ∀ i : ℕ,
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
      simp only [pow_zero, Nat.div_one, counterValue_cons]
      omega
    | succ i =>
      have hkey : counterValue (d :: u) / 3 ^ (i + 1) = counterValue u / 3 ^ i := by
        rw [pow_succ, counterValue_cons, mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      rw [hkey]
      exact ih hu' i

/-! ## Not halting while a cascade dies at a `4` -/

theorem iter_none (j : ℕ) : iter j none = none := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [iter] using ih

/-- If a configuration is still alive after `n` steps, it was alive at every
earlier time: no halt can have occurred in between. -/
theorem iter_isSome_of_le {c d : Cfg} {n : ℕ} (h : iter n (some c) = some d) {k : ℕ}
    (hk : k ≤ n) : iter k (some c) ≠ none := by
  intro hnone
  have : iter n (some c) = none := by
    rw [show n = k + (n - k) by omega, iter_add, hnone, iter_none]
  rw [h] at this
  exact Option.some_ne_none d this

/-- **A cascade that runs into a `4` is harmless.**  While a cascade crosses a
block of digits `0` and `2` with no two consecutive `2`s and reaches a cell
containing `4` (the digit `1`), the machine does not halt — at the `4` the
cascade is extinguished (see `cascade_P_four_stops`, `cascade_Q_four_stops`).
This is the exact complement of `cascade_halt_over_cantor_block`: a digit `1`
anywhere in the block saves the frontier. -/
theorem no_halt_of_cascade_into_four (c : Sym) (u l r : List Sym)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) :
    ∃ n : ℕ, (∀ k ≤ n, iter k (some ⟨St.A, u ++ (4 : Sym) :: l, c, (2 : Sym) :: r⟩) ≠ none) ∧
      ∃ (m' : Mode) (r' : List Sym),
        iter n (some ⟨St.A, u ++ (4 : Sym) :: l, c, (2 : Sym) :: r⟩)
          = some ⟨St.A, l, 4, m'.sym :: r'⟩ := by
  obtain ⟨n, m', r', hn⟩ := (cantor_traverse u c hc hu hno 4 l r).1
  exact ⟨n, fun k hk => iter_isSome_of_le hn hk, m', r', hn⟩

/-! ## Consequences for the machine started on the blank tape

The statements above are about arbitrary configurations.  They become
statements about the machine itself through the notion of reachability. -/

/-- A configuration is reachable if the machine started on the blank tape is in
it at some time. -/
def Reachable (c : Cfg) : Prop := ∃ n, run n = some c

theorem Reachable.iter {c d : Cfg} (h : Reachable c) {n : ℕ}
    (hn : iter n (some c) = some d) : Reachable d := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [run, iter_add, ← run, ht, hn]⟩

theorem halts_of_reachable {c : Cfg} (h : Reachable c) {n : ℕ}
    (hn : iter n (some c) = none) : Halts := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [run, iter_add, ← run, ht, hn]⟩

/-- **The Cantor halting criterion for the machine.**  If the machine ever
reaches a configuration in which a cascade (a left-moving `A` with a `2` to its
right) faces a block of counter digits `0` and `2` with no two consecutive
digits `2`, immediately followed by the frontier `1`, then the machine halts.

By `cantor_value`, the value of such a block is an integer none of whose
base-3 digits is `1` — a Cantor-set value. -/
theorem halts_of_reachable_cantor_block (c : Sym) (u l r : List Sym)
    (hreach : Reachable ⟨St.A, u ++ (1 : Sym) :: l, c, (2 : Sym) :: r⟩)
    (hc : c = 3 ∨ c = 0) (hu : ∀ s ∈ u, s = 3 ∨ s = 0)
    (hno : NoAdjacentZeros (c :: u)) : Halts := by
  obtain ⟨n, hn⟩ := cascade_halt_over_cantor_block c u l r hc hu hno
  exact halts_of_reachable hreach hn

/-- **The counter increment, as a statement about the machine.**  If the
machine reaches a configuration in which the head enters a non-saturated
counter word `d :: ds` from the right in state `B`, then it reaches the
configuration in which that word has been replaced by its increment — whose
value is one larger. -/
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

end TM2x5
