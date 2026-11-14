import RequestProject.Macro

/-!
# Exact return, overflow and productive-tail rules

DRAFT: this extension has NOT been compiled in the current environment.
No theorem here asserts that the blank orbit reaches the productive family.
The global blank-tape halting/nonhalting question is not settled by this file.

`RB` and `RA` are context-independent excursions exiting one cell to the left
in B and A, respectively. `BlankRB` allows consuming fresh blank cells to the
right. Its productive-family theorem is closure under a completed return,
NOT a reachability theorem for the blank initial configuration.
-/
namespace TM2x5.Overflow

abbrev RB (u v : List Sym) (n : Nat) : Prop :=
  ∀ (a : Sym) (l r : List Sym),
    iter n (some (onFirst St.A (a :: l) (u ++ r))) =
      some (Cfg.mk St.B l a (v ++ r))

abbrev RA (u v : List Sym) (n : Nat) : Prop :=
  ∀ (a : Sym) (l r : List Sym),
    iter n (some (onFirst St.A (a :: l) (u ++ r))) =
      some (Cfg.mk St.A l a (v ++ r))

theorem rb40 (w : List Sym) : RB (4 :: 0 :: w) (4 :: 2 :: w) 3 := by
  intro a l r
  rfl

theorem rb42 (w : List Sym) : RB (4 :: 2 :: w) (4 :: 4 :: w) 3 := by
  intro a l r
  rfl

theorem rb44 {u v : List Sym} {n : Nat} (h : RB u v n) :
    RB (4 :: 4 :: u) (4 :: 2 :: v) (n + 4) := by
  intro a l r
  have hs : iter 2 (some (onFirst St.A (a :: l) ((4 :: 4 :: u) ++ r))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    cases u ++ r <;> rfl
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 (v ++ r))) =
      some (Cfg.mk St.B l a ((4 :: 2 :: v) ++ r)) := rfl
  rw [show n + 4 = 2 + (n + 2) by omega, iter_add, hs, iter_add,
    h 0 ((2 : Sym) :: a :: l) r, he]

theorem rb43 {u v w : List Sym} {n m : Nat}
    (h1 : RB u v n) (h2 : RB v w m) :
    RB (4 :: 3 :: u) (4 :: 2 :: w) (n + m + 5) := by
  intro a l r
  have hs : iter 2 (some (onFirst St.A (a :: l) ((4 :: 3 :: u) ++ r))) =
      some (onFirst St.A ((4 : Sym) :: 2 :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    cases u ++ r <;> rfl
  have hm : iter 1 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 4 (v ++ r))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) (v ++ r)) := by
    cases v ++ r <;> rfl
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 (w ++ r))) =
      some (Cfg.mk St.B l a ((4 :: 2 :: w) ++ r)) := rfl
  rw [show n + m + 5 = 2 + (n + (1 + (m + 2))) by omega,
    iter_add, hs, iter_add, h1 4 ((2 : Sym) :: a :: l) r,
    iter_add, hm, iter_add, h2 0 ((2 : Sym) :: a :: l) r, he]

/-! The cascade collision rules, including the exceptional fresh-tape event. -/

theorem ra32 (w : List Sym) : RA (3 :: 2 :: w) (2 :: 2 :: w) 1 := by
  intro a l r
  rfl

theorem ra_wrap44 {u v : List Sym} {n : Nat} (h : RA u (2 :: v) n) :
    RA (4 :: 4 :: u) (2 :: 2 :: 4 :: v) (n + 8) := by
  intro a l r
  have hs : iter 2 (some (onFirst St.A (a :: l) ((4 :: 4 :: u) ++ r))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    cases u ++ r <;> rfl
  have he : iter 6 (some (Cfg.mk St.A ((2 : Sym) :: a :: l) 0 ((2 :: v) ++ r))) =
      some (Cfg.mk St.A l a ((2 :: 2 :: 4 :: v) ++ r)) := rfl
  rw [show n + 8 = 2 + (n + 6) by omega, iter_add, hs,
    iter_add, h 0 ((2 : Sym) :: a :: l) r, he]

def blocks44 : Nat → List Sym → List Sym
  | 0, w => w
  | n + 1, w => 4 :: 4 :: blocks44 n w

def blocks42 : Nat → List Sym → List Sym
  | 0, w => w
  | n + 1, w => 4 :: 2 :: blocks42 n w

theorem collide32 (n : Nat) :
    RA (blocks44 n [3, 2]) (2 :: 2 :: blocks42 n []) (8 * n + 1) := by
  induction n with
  | zero => exact ra32 []
  | succ n ih =>
    have h := ra_wrap44 ih
    convert h using 1 <;> simp [blocks44, blocks42] <;> omega

theorem fresh_base : RA [4, 4, 0, 0, 0, 0] [2, 2, 4, 4, 3, 2] 19 := by
  intro a l r
  rfl

theorem fresh_overflow (n : Nat) :
    RA (blocks44 (n + 1) [0, 0, 0, 0])
       (2 :: 2 :: blocks42 n [4, 4, 3, 2]) (8 * n + 19) := by
  induction n with
  | zero => exact fresh_base
  | succ n ih =>
    have h := ra_wrap44 ih
    convert h using 1 <;> simp [blocks44, blocks42] <;> omega

theorem productive_terminal_context :
    RB [4, 3, 2, 0, 0] [4, 4, 4, 3, 2] 11 := by
  intro a l r
  rfl

/-! Arithmetic behind the exact maximum-return capacity. -/

inductive Token
  | divThree | bitMinusOne | bitZero | bitOne | bitThree
  deriving DecidableEq, Repr

def capacity : List Token → Nat
  | [] => 0
  | Token.divThree :: xs => capacity xs / 3
  | Token.bitMinusOne :: xs => 2 * capacity xs + 2
  | Token.bitZero :: xs => 2 * capacity xs + 1
  | Token.bitOne :: xs => 2 * capacity xs
  | Token.bitThree :: xs => 2 * capacity xs - 2

theorem divThree_capacity (c k : Nat) : k ≤ c / 3 <-> 3 * k ≤ c := by omega

theorem minusOne_capacity (c k : Nat) (hk : 0 < k) :
    k ≤ 2 * c + 2 <-> (k - 1) / 2 ≤ c := by omega

theorem zero_capacity (c k : Nat) :
    k ≤ 2 * c + 1 <-> k / 2 ≤ c := by omega

theorem one_capacity (c k : Nat) :
    k ≤ 2 * c <-> (k + 1) / 2 ≤ c := by omega

theorem three_capacity (c k : Nat) (hk : 0 < k) :
    k ≤ 2 * c - 2 <-> (k + 3) / 2 ≤ c := by omega

theorem divThree_capacity_decreases (c k : Nat) (h : 3 * k ≤ c) :
    (c - 3 * k) / 3 = c / 3 - k := by omega

theorem bit_capacity_decreases (c k b : Nat) (h : (k + b) / 2 ≤ c) :
    2 * (c - (k + b) / 2) + 1 - (k + b) % 2 = (2 * c + 1 - b) - k := by
  omega

/-! A genuinely productive language on a blank right tail. -/

abbrev BlankRB (u v : List Sym) (n : Nat) : Prop :=
  ∀ (a : Sym) (l : List Sym),
    iter n (some (onFirst St.A (a :: l) u)) = some (Cfg.mk St.B l a v)

theorem blank_of_rb {u v : List Sym} {n : Nat} (h : RB u v n) :
    BlankRB u v n := by
  intro a l
  simpa using h a l []

theorem blank_terminal : BlankRB [4, 3, 2] [4, 4, 4, 3, 2] 11 := by
  intro a l
  rfl

theorem blank44 {u v : List Sym} {n : Nat} (h : BlankRB u v n) :
    BlankRB (4 :: 4 :: u) (4 :: 2 :: v) (n + 4) := by
  intro a l
  have hs : iter 2 (some (onFirst St.A (a :: l) (4 :: 4 :: u))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) u) := by
    cases u <;> rfl
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 v)) =
      some (Cfg.mk St.B l a (4 :: 2 :: v)) := rfl
  rw [show n + 4 = 2 + (n + 2) by omega, iter_add, hs, iter_add,
    h 0 ((2 : Sym) :: a :: l), he]

theorem blank43 {u v w : List Sym} {n m : Nat}
    (h1 : BlankRB u v n) (h2 : BlankRB v w m) :
    BlankRB (4 :: 3 :: u) (4 :: 2 :: w) (n + m + 5) := by
  intro a l
  have hs : iter 2 (some (onFirst St.A (a :: l) (4 :: 3 :: u))) =
      some (onFirst St.A ((4 : Sym) :: 2 :: a :: l) u) := by
    cases u <;> rfl
  have hm : iter 1 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 4 v)) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) v) := by
    cases v <;> rfl
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 w)) =
      some (Cfg.mk St.B l a (4 :: 2 :: w)) := rfl
  rw [show n + m + 5 = 2 + (n + (1 + (m + 2))) by omega,
    iter_add, hs, iter_add, h1 4 ((2 : Sym) :: a :: l),
    iter_add, hm, iter_add, h2 0 ((2 : Sym) :: a :: l), he]

theorem blank_two {u v w z : List Sym} {n1 n2 n3 : Nat}
    (h1 : BlankRB u v n1) (h2 : BlankRB v w n2) (h3 : BlankRB w z n3) :
    BlankRB (2 :: u) (2 :: z) (4 + n1 + n2 + n3) := by
  intro a l
  have hs : iter 1 (some (onFirst St.A (a :: l) (2 :: u))) =
      some (onFirst St.A ((3 : Sym) :: a :: l) u) := by
    cases u <;> rfl
  have h34 : iter 1 (some (Cfg.mk St.B (a :: l) 3 v)) =
      some (onFirst St.A ((4 : Sym) :: a :: l) v) := by
    cases v <;> rfl
  have h40 : iter 1 (some (Cfg.mk St.B (a :: l) 4 w)) =
      some (onFirst St.A ((0 : Sym) :: a :: l) w) := by
    cases w <;> rfl
  have he : iter 1 (some (Cfg.mk St.B (a :: l) 0 z)) =
      some (Cfg.mk St.B l a (2 :: z)) := rfl
  rw [show 4 + n1 + n2 + n3 = 1 + (n1 + (1 + (n2 + (1 + (n3 + 1))))) by omega,
    iter_add, hs, iter_add, h1 3 (a :: l), iter_add, h34,
    iter_add, h2 4 (a :: l), iter_add, h40, iter_add, h3 0 (a :: l), he]

/-- Grade counts `2` tokens plus `43` tokens, not ordinary binary pairs. -/
inductive Productive : List Sym → Nat → Prop
  | terminal : Productive [4, 3, 2] 0
  | minus {w : List Sym} {k : Nat} : Productive w k → Productive (4 :: 0 :: w) k
  | zero {w : List Sym} {k : Nat} : Productive w k → Productive (4 :: 2 :: w) k
  | one {w : List Sym} {k : Nat} : Productive w k → Productive (4 :: 4 :: w) k
  | two {w : List Sym} {k : Nat} : Productive w k → Productive (2 :: w) (k + 1)
  | three {w : List Sym} {k : Nat} : Productive w k → Productive (4 :: 3 :: w) (k + 1)

abbrev ProductiveReturn (w : List Sym) (k : Nat) : Prop :=
  ∃ (v : List Sym) (j n : Nat), Productive v j ∧ j ≤ k ∧
    0 < n ∧ BlankRB w v n

/-- Draft closure proof: each productive word makes a positive-time return
and remains productive. The strong outer induction justifies repeated calls
on a child even when its binary suffix has grown. -/
theorem productive_return_bounded (k : Nat) :
    ∀ (w : List Sym) (j : Nat), Productive w j → j ≤ k ->
      ProductiveReturn w j := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro w j hw
    induction hw with
    | terminal =>
      intro _
      exact ⟨[4, 4, 4, 3, 2], 0, 11, Productive.one Productive.terminal,
        Nat.le_refl _, by omega, blank_terminal⟩
    | @minus w j hw ihw =>
      intro _
      exact ⟨4 :: 2 :: w, j, 3, Productive.zero hw, Nat.le_refl _,
        by omega, blank_of_rb (rb40 w)⟩
    | @zero w j hw ihw =>
      intro _
      exact ⟨4 :: 4 :: w, j, 3, Productive.one hw, Nat.le_refl _,
        by omega, blank_of_rb (rb42 w)⟩
    | @one w j hw ihw =>
      intro hjk
      obtain ⟨v, j', n, hv, hj', hn, hr⟩ := ihw hjk
      exact ⟨4 :: 2 :: v, j', n + 4, Productive.zero hv, hj',
        by omega, blank44 hr⟩
    | @two w j hw ihw =>
      intro hjk
      have hjlt : j < k := by omega
      obtain ⟨v1, j1, n1, hv1, hj1, hn1, hr1⟩ := ih j hjlt w j hw (Nat.le_refl _)
      obtain ⟨v2, j2, n2, hv2, hj2, hn2, hr2⟩ := ih j hjlt v1 j1 hv1 hj1
      have hj2' : j2 ≤ j := Nat.le_trans hj2 hj1
      obtain ⟨v3, j3, n3, hv3, hj3, hn3, hr3⟩ := ih j hjlt v2 j2 hv2 hj2'
      refine ⟨2 :: v3, j3 + 1, 4 + n1 + n2 + n3, Productive.two hv3, ?_, ?_,
        blank_two hr1 hr2 hr3⟩ <;> omega
    | @three w j hw ihw =>
      intro hjk
      have hjlt : j < k := by omega
      obtain ⟨v1, j1, n1, hv1, hj1, hn1, hr1⟩ := ih j hjlt w j hw (Nat.le_refl _)
      obtain ⟨v2, j2, n2, hv2, hj2, hn2, hr2⟩ := ih j hjlt v1 j1 hv1 hj1
      refine ⟨4 :: 2 :: v2, j2, n1 + n2 + 5, Productive.zero hv2, ?_, ?_,
        blank43 hr1 hr2⟩ <;> omega

theorem productive_return {w : List Sym} {k : Nat} (h : Productive w k) :
    ProductiveReturn w k := productive_return_bounded k w k h (Nat.le_refl _)

end TM2x5.Overflow
