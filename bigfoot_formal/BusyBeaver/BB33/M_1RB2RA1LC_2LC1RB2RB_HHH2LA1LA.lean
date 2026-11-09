/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB2RA1LC_2LC1RB2RB_---2LA1LA` (Bigfoot, Holdout #829)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
3-state, 3-symbol Busy Beaver holdout `1RB2RA1LC_2LC1RB2RB_---2LA1LA` (**Bigfoot**, Holdout #829;
discovered and analyzed by Shawn Ligocki and savask in October 2023, see
<https://wiki.bbchallenge.org/wiki/Bigfoot> and
<https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html>).

Starting from the blank tape (`init []`), the trajectory reaches the single canonical family
$$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty
  \quad (a, b, c \in \mathbb{N})$$
at $A(2, 0, 0)$ in 69 raw Turing machine steps. Every configuration $A(a, b, c)$ advances in
`ReachesPlus` according to $b \bmod 6 = 6q + r$:

## Collatz-like Acceleration Rules

```text
Configuration family:
  A(a, b, c) = 0^inf (12)^a 1^(2b+2) <A 1^(2(c+2)) 0^inf

Mod-6 transition rules (b = 6q + r):
  A(a,   6q,   c) -> A(a+1, 8q+c,   1)
  A(0,   6q+1, c) -> Halt (C0)
  A(a+1, 6q+1, c) -> A(a,   8q+c+4, 0)
  A(a,   6q+2, c) -> A(a,   8q+c+2, 3)
  A(a,   6q+3, c) -> A(a+1, 8q+c+4, 0)
  A(a,   6q+4, c) -> A(a,   8q+c+6, 1)
  A(a,   6q+5, c) -> A(a,   8q+c+8, 0)

Start: A(2, 0, 0) at step 69
Orbit: (2,0,0) -> (3,0,1) -> (4,1,1) -> (3,5,0) -> (3,8,0) -> (3,10,3) -> (3,17,1)
    -> (3,25,0) -> (2,36,0) -> ...
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA

open ThreeState Turing

/-- The `(3, 3)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2RA1LC_2LC1RB2RB_---2LA1LA"

/-- The `(3, 3)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

/-! ## Level B: Collatz-like Acceleration (`State`, `start`, `encode`, `next`) -/

/-- Canonical configuration family
$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty$. -/
inductive State where
  | A (a b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial accelerated state $A(2, 0, 0)$, reached from `init []` in 69 steps. -/
def start : State := .A 2 0 0

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
@[simp]
def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a b c =>
      Cfg.headLeft A
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * b + 2)))
        (([1] : List (Fin 3)) ^ (2 * (c + 2)) +> default)

/-- Ligocki and savask's 7-rule mod-6 Collatz-like map for Bigfoot (`none` indicates halting at
$a = 0, b \equiv 1 \pmod 6$). -/
def next : State → Option State
  | .A a b c =>
      let q := b / 6
      let r := b % 6
      if r = 0 then
        some (.A (a + 1) (8 * q + c) 1)
      else if r = 1 then
        match a with
        | 0 => none
        | a' + 1 => some (.A a' (8 * q + c + 4) 0)
      else if r = 2 then
        some (.A a (8 * q + c + 2) 3)
      else if r = 3 then
        some (.A (a + 1) (8 * q + c + 4) 0)
      else if r = 4 then
        some (.A a (8 * q + c + 6) 1)
      else
        some (.A a (8 * q + c + 8) 0)

/-! ## Elementary Shift Rules and Tape Block Identities -/

@[simp]
private theorem pair_one_pow (k : ℕ) :
    ([1, 1] : List (Fin 3)) ^ k = ([1] : List (Fin 3)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 1 k

@[simp]
private theorem pair_two_pow (k : ℕ) :
    ([2, 2] : List (Fin 3)) ^ k = ([2] : List (Fin 3)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 2 k

private theorem flip_12_21 (a : ℕ) :
    ((default <+ ([1] : List (Fin 3))) <+ ([1, 2] : List (Fin 3)) ^ a) =
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3))) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have h1 : ([1, 2] : List (Fin 3)) ^ (a + 1) =
        ([1, 2] : List (Fin 3)) ++ ([1, 2] : List (Fin 3)) ^ a := rfl
    rw [h1, ← ListBlank.append_append, ih, ListBlank.append_append]
    have h12 : ([1, 2] : List (Fin 3)) ++ ([1] : List (Fin 3)) =
        ([1] : List (Fin 3)) ++ ([2, 1] : List (Fin 3)) := rfl
    rw [h12, ← ListBlank.append_append, ListBlank.append_append]
    rfl

private theorem shift_A_1 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{A}}> (([1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([2] : List (Fin 3)) ^ k) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([2] : List (Fin 3))) {{A}}> (([1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([2] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([2] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ k) =
        (l <+ ([2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_C_22 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([2, 2] : List (Fin 3)) ^ k) <{{C}} r) [target]⊢*
      (l <{{C}} (([1, 1] : List (Fin 3)) ^ k +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (((l <+ ([2, 2] : List (Fin 3)) ^ k) <+ ([2, 2] : List (Fin 3))) <{{C}} r)
        [target]⊢⁺ ((l <+ ([2, 2] : List (Fin 3)) ^ k) <{{C}} (([1, 1] : List (Fin 3)) +> r)) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([2, 2] : List (Fin 3)) ^ k) <+ ([2, 2] : List (Fin 3))) =
        (l <+ ([2, 2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([1, 1] : List (Fin 3)) ^ k +> (([1, 1] : List (Fin 3)) +> r)) =
        (([1, 1] : List (Fin 3)) ^ (k + 1) +> r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

private theorem shift_A_21 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([2, 1] : List (Fin 3)) ^ k) <{{A}} r) [target]⊢*
      (l <{{A}} (([2, 1] : List (Fin 3)) ^ k +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (((l <+ ([2, 1] : List (Fin 3)) ^ k) <+ ([2, 1] : List (Fin 3))) <{{A}} r)
        [target]⊢⁺ ((l <+ ([2, 1] : List (Fin 3)) ^ k) <{{A}} (([2, 1] : List (Fin 3)) +> r)) := by
      bb_steps
    have h2 := ih l (([2, 1] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([2, 1] : List (Fin 3)) ^ k) <+ ([2, 1] : List (Fin 3))) =
        (l <+ ([2, 1] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([2, 1] : List (Fin 3)) ^ k +> (([2, 1] : List (Fin 3)) +> r)) =
        (([2, 1] : List (Fin 3)) ^ (k + 1) +> r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

private theorem shift_B_21 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{B}}> (([2, 1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([1, 2] : List (Fin 3)) ^ k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{B}}> (([2, 1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 2] : List (Fin 3))) {{B}}> (([2, 1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([1, 2] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1, 2] : List (Fin 3))) <+ ([1, 2] : List (Fin 3)) ^ k) =
        (l <+ ([1, 2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_B_1 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{B}}> (([1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([1] : List (Fin 3)) ^ k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{B}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1] : List (Fin 3))) {{B}}> (([1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([1] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ k) =
        (l <+ ([1] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-! ## Bounce and Drain Combinators -/

private theorem bounce_A0 (l : ListBlank (Fin 3)) (k : ℕ) :
    (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> default)) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1, 2, 2] : List (Fin 3)) +> default)) := by
  have h1 := shift_A_1 (k + 1) l default
  have h_l : (l <+ ([2] : List (Fin 3)) ^ (k + 1)) = ((l <+ ([2] : List (Fin 3)) ^ k) <+ [2]) := by
    rw [ListBlank.append_append]; rfl
  rw [h_l] at h1
  have h2 : (((l <+ ([2] : List (Fin 3)) ^ k) <+ [2]) {{A}}> default) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1, 2, 2] : List (Fin 3)) +> default)) := by
    bb_steps
  exact h1.trans_plus h2

private theorem bounce_A2 (l r : ListBlank (Fin 3)) (k : ℕ) :
    (l {{A}}> (([1] : List (Fin 3)) ^ k +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1] : List (Fin 3)) +> r)) := by
  have h1 := shift_A_1 k l (([2] : List (Fin 3)) +> r)
  have h2 : ((l <+ ([2] : List (Fin 3)) ^ k) {{A}}> (([2] : List (Fin 3)) +> r)) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1] : List (Fin 3)) +> r)) := by
    bb_steps
  exact h1.trans_plus h2

private theorem eat_even (l r : ListBlank (Fin 3)) (k : ℕ) :
    (((l <+ ([1, 1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * k)) <{{C}} r) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * k + 2) +> r)) := by
  rw [← pair_two_pow]
  have h1 := shift_C_22 k (l <+ ([1, 1] : List (Fin 3))) r
  rw [pair_one_pow] at h1
  have h2 : ((l <+ ([1, 1] : List (Fin 3))) <{{C}} (([1] : List (Fin 3)) ^ (2 * k) +> r))
      [target]⊢⁺
      (l <{{A}} (([1, 1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_r : (([1, 1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r)) =
      (([1] : List (Fin 3)) ^ (2 * k + 2) +> r) := by
    have h11 : ([1, 1] : List (Fin 3)) = ([1] : List (Fin 3)) ^ 2 := rfl
    rw [h11, ← ListBlank.append_pow_add]
    exact congrArg (fun m => ([1] : List (Fin 3)) ^ m +> r) (by omega)
  rwa [h_r] at h3

private theorem eat_odd (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([2] : List (Fin 3)) ^ (2 * k + 1)) <{{C}} r) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * k + 1) +> r)) := by
  have h_l : (l <+ ([2] : List (Fin 3)) ^ (2 * k + 1)) =
      ((l <+ [2]) <+ ([2, 2] : List (Fin 3)) ^ k) := by
    rw [pair_two_pow, ListBlank.append_append, ← list_pow_succ']
  rw [h_l]
  have h1 := shift_C_22 k (l <+ [2]) r
  rw [pair_one_pow] at h1
  have h2 : ((l <+ [2]) <{{C}} (([1] : List (Fin 3)) ^ (2 * k) +> r)) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_r : (([1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r)) =
      (([1] : List (Fin 3)) ^ (2 * k + 1) +> r) := rfl
  rwa [h_r] at h3

private theorem bounce_left_21 (a : ℕ) (r : ListBlank (Fin 3)) :
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}} r) [target]⊢⁺
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3))) {{B}}> r) := by
  have h1 := shift_A_21 a default r
  have h2 : (default <{{A}} (([2, 1] : List (Fin 3)) ^ a +> r)) [target]⊢⁺
      ((default <+ ([1] : List (Fin 3))) {{B}}> (([2, 1] : List (Fin 3)) ^ a +> r)) := by
    bb_steps
  have h3 := shift_B_21 a (default <+ ([1] : List (Fin 3))) r
  have h4 := (h1.trans_plus h2).trans_star h3
  rwa [flip_12_21 a] at h4

private theorem bounce_B_0 (l : ListBlank (Fin 3)) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) {{B}}> default) [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem bounce_B_22 (l : ListBlank (Fin 3)) :
    (((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([2, 2] : List (Fin 3))) {{B}}> default) [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem bounce_B_2 (l : ListBlank (Fin 3)) :
    (((l <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) <+ ([2] : List (Fin 3))) {{B}}> default)
        [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem append_one_pow_succ (k : ℕ) (r : ListBlank (Fin 3)) :
    (([1] : List (Fin 3)) ^ k +> (([1] : List (Fin 3)) +> r)) =
      (([1] : List (Fin 3)) ^ (k + 1) +> r) :=
  ListBlank.append_pow_succ' [1] k r

private theorem flip_A_head (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ k +> r)) =
      (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) := by
  rw [ListBlank.append_pow_succ]
  exact Cfg.headLeft_cons A 1 l _

private theorem flip_A_head3 (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ k +> r)) =
      ((l <+ ([1, 1] : List (Fin 3))) {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) :=
  flip_A_head (l <+ ([1, 1] : List (Fin 3))) r k

private theorem step_even_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 3) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head3 l default (2 * m)]
  have h1 := bounce_A0 (l <+ ([1, 1] : List (Fin 3))) (2 * m)
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h1
  have h2 := eat_even l (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 2)] at h3

private theorem step_even_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 5) +> r)) := by
  rw [flip_A_head3 l (([2] : List (Fin 3)) +> r) (2 * m + 1)]
  have h1 := bounce_A2 (l <+ ([1, 1] : List (Fin 3))) r (2 * m + 2)
  have hr2 : (2 * m + 2) = 2 * (m + 1) := by omega
  rw [hr2] at h1
  have h2 := eat_even l (([1] : List (Fin 3)) +> r) (m + 1)
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * (m + 1) + 2)] at h3

private theorem step_odd_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 2) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head l default (2 * m + 1)]
  have h1 := bounce_A0 l (2 * m + 1)
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h1
  have h2 := eat_odd l (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 1)] at h3

private theorem step_odd_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 2) +> r)) := by
  rw [flip_A_head l (([2] : List (Fin 3)) +> r) (2 * m)]
  have h1 := bounce_A2 l r (2 * m + 1)
  have h2 := eat_odd l (([1] : List (Fin 3)) +> r) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 1)] at h3

private theorem half_even_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default)) [target]⊢⁺
      (l <{{C}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head l default (2 * m)]
  have h1 := bounce_A0 l (2 * m)
  rw [← pair_two_pow] at h1
  have h2 := shift_C_22 m l (([1, 2, 2] : List (Fin 3)) +> default)
  rw [pair_one_pow] at h2
  have h3 := h1.trans_star h2
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h3
  rwa [append_one_pow_succ (2 * m)] at h3

private theorem half_even_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{C}} (([1] : List (Fin 3)) ^ (2 * m + 3) +> r)) := by
  rw [flip_A_head l (([2] : List (Fin 3)) +> r) (2 * m + 1)]
  have h1 := bounce_A2 l r (2 * (m + 1))
  rw [← pair_two_pow] at h1
  have h2 := shift_C_22 (m + 1) l (([1] : List (Fin 3)) +> r)
  rw [pair_one_pow] at h2
  have h3 := h1.trans_star h2
  rwa [append_one_pow_succ (2 * (m + 1))] at h3

private theorem pass_even (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3)) ^ 9) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 11) +> default)) := by
  have hl : (l <+ ([1] : List (Fin 3)) ^ 9) =
      (((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0 ((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) m
  have hr1 : 2 * m + 3 = 2 * (m + 1) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (l <+ ([1, 1, 1] : List (Fin 3))) (([2] : List (Fin 3)) +> default) (m + 1)
  have hr2 : 2 * (m + 1) + 5 = 2 * (m + 3) + 1 := by omega
  rw [hr2] at h2
  have h3 := step_even_2 l default (m + 3)
  have hr3 : 2 * (m + 3) + 5 = 2 * m + 11 := by omega
  rw [hr3] at h3
  exact (h1.trans h2).trans h3

private theorem pass_odd (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 6) +> default)) := by
  have hl : (l <+ ([1, 1, 1] : List (Fin 3))) = (((l <+ [1]) <+ [1]) <+ [1]) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_odd_0 ((l <+ [1]) <+ [1]) m
  have hr1 : 2 * m + 2 = 2 * (m + 1) := by omega
  rw [hr1] at h1
  have h2 := step_odd_2 (l <+ [1]) (([2] : List (Fin 3)) +> default) (m + 1)
  have hr2 : 2 * (m + 1) + 2 = 2 * (m + 2) := by omega
  rw [hr2] at h2
  have h3 := step_odd_2 l default (m + 2)
  have hr3 : 2 * (m + 2) + 2 = 2 * m + 6 := by omega
  rw [hr3] at h3
  exact (h1.trans h2).trans h3

private theorem drain_step (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3)) ^ 12) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * (m + 8)) +> default)) := by
  have hl : (l <+ ([1] : List (Fin 3)) ^ 12) =
      ((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ 9) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := pass_even (l <+ ([1, 1, 1] : List (Fin 3))) m
  have hr1 : 2 * m + 11 = 2 * (m + 5) + 1 := by omega
  rw [hr1] at h1
  have h2 := pass_odd l (m + 5)
  have hr2 : 2 * (m + 5) + 6 = 2 * (m + 8) := by omega
  rw [hr2] at h2
  exact h1.trans h2

/-! ## Canonical Configuration Family and Mod-6 Macro Rules -/

private def cfg_mid (a b n : ℕ) : Cfg (Fin 3) (Fin 3) :=
  (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * b + 2)) <{{A}}
    (([1] : List (Fin 3)) ^ (2 * n) +> default))

private def cfg_A (a b c : ℕ) : Cfg (Fin 3) (Fin 3) :=
  cfg_mid a b (c + 2)

private theorem drain_mod6 (a q r n : ℕ) :
    (cfg_mid a (6 * q + r) n) [target]⊢* (cfg_mid a r (8 * q + n)) := by
  induction q generalizing n with
  | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add]
  | succ q ih =>
    have hl : 2 * (6 * (q + 1) + r) + 2 = 12 + (2 * (6 * q + r) + 2) := by omega
    unfold cfg_mid
    rw [hl, list_pow_add, ← ListBlank.append_append]
    have h1 := drain_step
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (6 * q + r) + 2)) n
    have h2 := ih (n + 8)
    have hr : 8 * q + (n + 8) = 8 * (q + 1) + n := by omega
    rw [hr] at h2
    exact (h1.trans_star h2).to_star

private theorem combine_B_ones (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ m) =
      (l <+ ([1] : List (Fin 3)) ^ (m + 1)) := by
  rw [ListBlank.append_append, ← list_pow_succ']

private theorem split_ones_left (l : ListBlank (Fin 3)) (m c k : ℕ) (h : m = c + k) :
    (l <+ ([1] : List (Fin 3)) ^ m) =
      ((l <+ ([1] : List (Fin 3)) ^ k) <+ ([1] : List (Fin 3)) ^ c) := by
  rw [ListBlank.append_append, h, list_pow_add]

private theorem base_0 (a n : ℕ) :
    (cfg_mid a 0 (n + 2)) [target]⊢⁺ (cfg_A (a + 1) n 1) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 2) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := half_even_0 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have h2 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}}
      (([2] : List (Fin 3)) +>
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))) := by
    bb_steps
  have h3 := bounce_left_21 a
    (([2] : List (Fin 3)) +>
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))
  have h4 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) {{B}}>
      (([2] : List (Fin 3)) +>
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default))))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) {{B}}>
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default))) := by
    have h21 : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    rw [h21]
    bb_steps
  have h5 := shift_B_1 (2 * (n + 2) + 1) (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
    (([2, 2] : List (Fin 3)) +> default)
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
      (2 * (n + 2) + 1) 3 (2 * n + 2) (by omega)] at h5
  have h6 : ((((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+
        ([1] : List (Fin 3)) ^ (2 * n + 2)) <+ ([1, 1, 1] : List (Fin 3))) {{B}}>
      (([2, 2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+
        ([1] : List (Fin 3)) ^ (2 * n + 2)) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([2, 2] : List (Fin 3))) {{B}}> default) := by
    bb_steps
  have h7 := bounce_B_22
    ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+ ([1] : List (Fin 3)) ^ (2 * n + 2))
  exact ((h1.trans h2).trans (h3.trans h4)).trans (h5.trans_plus (h6.trans h7))

private theorem base_1_pre (a n : ℕ) :
    (cfg_mid a 1 (n + 2)) [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{C}}
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))) := by
  unfold cfg_mid
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 4) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := half_even_2 (default <+ ([2, 1] : List (Fin 3)) ^ a)
    (([2] : List (Fin 3)) +> default) (n + 3)
  have hr2 : 2 * (n + 3) + 3 = 2 * (n + 2) + 5 := by omega
  rw [hr2] at h2
  exact h1.trans h2

private theorem base_1_halt (n : ℕ) :
    ∃ cfg', ((cfg_mid 0 1 (n + 2)) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(default <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))),
    base_1_pre 0 n, by bb_halt⟩

private theorem base_1_step (a n : ℕ) :
    (cfg_mid (a + 1) 1 (n + 2)) [target]⊢⁺ (cfg_A a (n + 4) 0) := by
  have h1 := base_1_pre (a + 1) n
  have h2 : ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default)))
      [target]⊢⁺
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{A}}
      (([1] : List (Fin 3)) ^ (2 * (n + 5)) +> (([2] : List (Fin 3)) +> default))) := by
    have hl : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    have hr : (([1] : List (Fin 3)) ^ (2 * (n + 5)) +> (([2] : List (Fin 3)) +> default)) =
        (([1] : List (Fin 3)) +>
          (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))) := by
      have he : 2 * (n + 5) = 1 + (2 * (n + 2) + 5) := by omega
      rw [he, ListBlank.append_pow_add]; rfl
    rw [hl, hr]
    bb_steps
  have h3 := step_odd_2 (default <+ ([2, 1] : List (Fin 3)) ^ a) default (n + 5)
  have h4 := bounce_left_21 a (([1] : List (Fin 3)) ^ (2 * (n + 5) + 2) +> default)
  have h5 := shift_B_1 (2 * (n + 5) + 2)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default
  rw [combine_B_ones] at h5
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 5) + 2) + 1) 3 (2 * (n + 4) + 2) (by omega)] at h5
  have h6 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 4) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans (h5.trans_plus h6)))

private theorem base_2 (a n : ℕ) :
    (cfg_mid a 2 (n + 2)) [target]⊢⁺ (cfg_A a (n + 2) 3) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 6) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1, 1, 1] : List (Fin 3))) (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (default <+ ([2, 1] : List (Fin 3)) ^ a)
    (([2] : List (Fin 3)) +> default) (n + 3)
  have h3 := bounce_left_21 a
    (([1] : List (Fin 3)) ^ (2 * (n + 3) + 5) +> (([2] : List (Fin 3)) +> default))
  have h4 := shift_B_1 (2 * (n + 3) + 5)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (([2] : List (Fin 3)) +> default)
  rw [combine_B_ones] at h4
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 3) + 5) + 1) 6 (2 * (n + 2) + 2) (by omega)] at h4
  have h5 : ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2)) <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) {{B}}>
      (([2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2)) <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) <+
        [2]) {{B}}> default) := by
    bb_steps
  have h6 := bounce_B_2
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans_plus (h5.trans h6)))

private theorem base_3 (a n : ℕ) :
    (cfg_mid a 3 (n + 2)) [target]⊢⁺ (cfg_A (a + 1) (n + 4) 0) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 8) =
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) <+
        ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0
    ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) <+ ([1, 1, 1] : List (Fin 3)))
    (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1])
    (([2] : List (Fin 3)) +> default) (n + 3)
  have hr2 : 2 * (n + 3) + 5 = 2 * (n + 5) + 1 := by omega
  rw [hr2] at h2
  have h3 := half_even_2 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default (n + 5)
  have h4 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)) [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}}
      (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default))) := by
    bb_steps
  have h5 := bounce_left_21 a
    (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default))
  have h6 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) {{B}}>
      (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) {{B}}>
      (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)) := by
    have h21 : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    rw [h21]
    bb_steps
  have h7 := shift_B_1 (2 * (n + 5) + 3)
    (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) default
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
      (2 * (n + 5) + 3) 3 (2 * (n + 4) + 2) (by omega)] at h7
  have h8 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+ ([1] : List (Fin 3)) ^ (2 * (n + 4) + 2))
  exact ((h1.trans h2).trans (h3.trans h4)).trans ((h5.trans h6).trans (h7.trans_plus h8))

private theorem base_4 (a n : ℕ) :
    (cfg_mid a 4 (n + 2)) [target]⊢⁺ (cfg_A a (n + 6) 1) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 10) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ ([1] : List (Fin 3)) ^ 9) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := pass_even ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have hr1 : 2 * (n + 2) + 11 = 2 * (n + 7) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_odd_0 (default <+ ([2, 1] : List (Fin 3)) ^ a) (n + 7)
  have h3 := bounce_left_21 a
    (([1] : List (Fin 3)) ^ (2 * (n + 7) + 2) +> (([2, 2] : List (Fin 3)) +> default))
  have h4 := shift_B_1 (2 * (n + 7) + 2)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (([2, 2] : List (Fin 3)) +> default)
  rw [combine_B_ones] at h4
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 7) + 2) + 1) 3 (2 * (n + 6) + 2) (by omega)] at h4
  have h5 : ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2)) <+ ([1, 1, 1] : List (Fin 3))) {{B}}>
      (([2, 2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2)) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([2, 2] : List (Fin 3))) {{B}}> default) := by
    bb_steps
  have h6 := bounce_B_22
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans_plus (h5.trans h6)))

private theorem base_5 (a n : ℕ) :
    (cfg_mid a 5 (n + 2)) [target]⊢⁺ (cfg_A a (n + 8) 0) := by
  unfold cfg_mid cfg_A
  have h1 := drain_step (default <+ ([2, 1] : List (Fin 3)) ^ a) (n + 2)
  have h2 := bounce_left_21 a (([1] : List (Fin 3)) ^ (2 * ((n + 2) + 8)) +> default)
  have h3 := shift_B_1 (2 * ((n + 2) + 8))
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default
  rw [combine_B_ones] at h3
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      (2 * ((n + 2) + 8) + 1) 3 (2 * (n + 8) + 2) (by omega)] at h3
  have h4 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 8) + 2))
  exact h1.trans (h2.trans (h3.trans_plus h4))

private theorem rule_mod6_0 (a q c : ℕ) :
    (cfg_A a (6 * q + 0) c) [target]⊢⁺ (cfg_A (a + 1) (8 * q + c) 1) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 0 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_0 a (8 * q + c))

private theorem rule_mod6_1_halt (q c : ℕ) :
    ∃ cfg', ((cfg_A 0 (6 * q + 1) c) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  unfold cfg_A
  have h1 := drain_mod6 0 q 1 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  obtain ⟨cfg', h2, hnone⟩ := base_1_halt (8 * q + c)
  exact ⟨cfg', h1.trans_plus h2, hnone⟩

private theorem rule_mod6_1_step (a q c : ℕ) :
    (cfg_A (a + 1) (6 * q + 1) c) [target]⊢⁺ (cfg_A a (8 * q + c + 4) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 (a + 1) q 1 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_1_step a (8 * q + c))

private theorem rule_mod6_2 (a q c : ℕ) :
    (cfg_A a (6 * q + 2) c) [target]⊢⁺ (cfg_A a (8 * q + c + 2) 3) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 2 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_2 a (8 * q + c))

private theorem rule_mod6_3 (a q c : ℕ) :
    (cfg_A a (6 * q + 3) c) [target]⊢⁺ (cfg_A (a + 1) (8 * q + c + 4) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 3 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_3 a (8 * q + c))

private theorem rule_mod6_4 (a q c : ℕ) :
    (cfg_A a (6 * q + 4) c) [target]⊢⁺ (cfg_A a (8 * q + c + 6) 1) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 4 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_4 a (8 * q + c))

private theorem rule_mod6_5 (a q c : ℕ) :
    (cfg_A a (6 * q + 5) c) [target]⊢⁺ (cfg_A a (8 * q + c + 8) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 5 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_5 a (8 * q + c))

private theorem mod6_cases (b : ℕ) :
    (b = 6 * (b / 6) + 0) ∨ (b = 6 * (b / 6) + 1) ∨ (b = 6 * (b / 6) + 2) ∨
    (b = 6 * (b / 6) + 3) ∨ (b = 6 * (b / 6) + 4) ∨ (b = 6 * (b / 6) + 5) := by
  omega

private theorem init_to_cfg_A : (init []) [target]⊢⁺ (cfg_A 2 0 0) := by
  unfold cfg_A cfg_mid
  bb_steps

private theorem step_state_plus (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, b, c⟩
  dsimp only [next]
  rcases mod6_cases b with h0 | h1 | h2 | h3 | h4 | h5
  · have hr : b % 6 = 0 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A (a + 1) (8 * (b / 6) + c) 1)
    set q := b / 6
    rw [h0]
    exact rule_mod6_0 a q c
  · have hr : b % 6 = 1 := by omega
    rw [hr]
    rcases a with _ | a'
    · change ∃ cfg', ((cfg_A 0 b c) [target]⊢⁺ cfg') ∧ (step target cfg').isNone
      set q := b / 6
      rw [h1]
      exact rule_mod6_1_halt q c
    · change (cfg_A (a' + 1) b c) [target]⊢⁺ (cfg_A a' (8 * (b / 6) + c + 4) 0)
      set q := b / 6
      rw [h1]
      exact rule_mod6_1_step a' q c
  · have hr : b % 6 = 2 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 2) 3)
    set q := b / 6
    rw [h2]
    exact rule_mod6_2 a q c
  · have hr : b % 6 = 3 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A (a + 1) (8 * (b / 6) + c + 4) 0)
    set q := b / 6
    rw [h3]
    exact rule_mod6_3 a q c
  · have hr : b % 6 = 4 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 6) 1)
    set q := b / 6
    rw [h4]
    exact rule_mod6_4 a q c
  · have hr : b % 6 = 5 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 8) 0)
    set q := b / 6
    rw [h5]
    exact rule_mod6_5 a q c

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_to_cfg_A.to_star (fun s => ?_)
  have hs := step_state_plus s
  rcases hnext : next s with _ | s'
  · rw [hnext] at hs
    obtain ⟨cfg', hplus, hnone⟩ := hs
    exact ⟨cfg', hplus.to_star, hnone⟩
  · rw [hnext] at hs
    exact hs

/-- `target` halts iff the accelerated transition function `next` halts from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Level A: Closed `TapePatternSet` (`HasCollatzReduction`) -/

/-- Tape pattern for
$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty$. -/
def pat_A : TapePattern (Fin 3) (Fin 3) :=
  { left := .sym 1 (.rep [1, 1] 1 (.rep [2, 1] 0 .default))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 2 .default))))) }

/-- Full `TapePatternSet` for `1RB2RA1LC_2LC1RB2RB_---2LA1LA`. -/
def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A, .true)]

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = encode (.A (vars 0) (vars 1) (vars 2)) := by
  dsimp only [pat_A, evalTapePattern, evalTapeExpr, encode, Cfg.headRight, Cfg.headLeft]
  have hl : ([1] : List (Fin 3)) ^ (2 * vars 1 + 2) =
      1 :: 1 :: ([1, 1] : List (Fin 3)) ^ (vars 1) := by
    rw [pair_one_pow]
    have h2 : 2 * vars 1 + 2 = 2 + 2 * vars 1 := by omega
    rw [h2, list_pow_add]; rfl
  have hr : ([1] : List (Fin 3)) ^ (2 * (vars 2 + 2)) =
      1 :: 1 :: 1 :: 1 :: ([1, 1] : List (Fin 3)) ^ (vars 2) := by
    rw [pair_one_pow]
    have h4 : 2 * (vars 2 + 2) = 4 + 2 * vars 2 := by omega
    rw [h4, list_pow_add]; rfl
  rw [hl, hr]
  simp only [ListBlank.append_cons, ListBlank.head_cons, ListBlank.tail_cons]

private theorem mem_encode (s : State) : IsInPatternSet ps (encode s) := by
  rcases s with ⟨a, b, c⟩
  let vars : ℕ → ℕ := fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0
  refine ⟨(pat_A, .true), List.Mem.head _, vars, ?_, trivial⟩
  exact (eval_pat_A vars).symm

private theorem encode_of_mem (cfg : Cfg (Fin 3) (Fin 3))
    (h : IsInPatternSet ps cfg) : ∃ s : State, cfg = encode s := by
  rcases h with ⟨entry, hentry, vars, rfl, _⟩
  rcases List.mem_singleton.mp hentry with rfl
  exact ⟨.A (vars 0) (vars 1) (vars 2), eval_pat_A vars⟩

/-- `ps` is a closed pattern set for `target`. -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine is_valid_acceleration.isClosedPatternSet mem_encode encode_of_mem (fun s hnext => ?_)
  have hs := step_state_plus s
  rw [hnext] at hs
  exact hs

/-- `target` has a Collatz-like reduction via `ps`. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Deviation-law assessment

Bigfoot is a base-6 Collatz cryptid, not a sweep transducer: `next` carries into `b` by
`b' = 8 * (b / 6) + c + k`, resets `c` to `0`, `1` or `3`, and moves `a` by at most one. There is no
word, no pass function and no "one block per sweep", hence no deviation position and no
`blocks = dev / p` law as in the stacked-transducer holdouts (`#397`, Wily Coyote `#531`/`#532`).

Measured on the orbit from `start` (400 macro steps): `b` grows from `0` to about `3.7e59` with a
least-squares log-slope of `0.288`, i.e. the exact exponential rate `ln(4/3)` per macro step
(`8/6 = 4/3`), and log-residual `0.000`; `a` stays below `70` and is not eventually affine; `c` is
confined to `{0, 1, 3}`. So the growth is multiplicative, not linear: no deviation law exists here.
-/

/-- Iterate the macro-step `n` times (`none` indicates halting). -/
def runMacro : ℕ → State → Option State
  | 0, s => some s
  | n + 1, s => (runMacro n s).bind next

/-- The first macro step from `start = A(2, 0, 0)`. -/
theorem step_start : next start = some (.A 3 0 1) := by decide

/-- Ten macro steps take `start = A(2, 0, 0)` to `A(4, 65, 1)`: `b` grows `0 -> 65`. -/
theorem runMacro_ten : runMacro 10 start = some (.A 4 65 1) := by decide

/-- One macro step carries `b` from `1` to `5` (`A(4, 1, 1) -> A(3, 5, 0)`). -/
theorem counter_jump : next (.A 4 1 1) = some (.A 3 5 0) := by decide


/-! ## Certified geometric growth of the `b`-counter

Every rule of `next` maps `b = 6q + r` (`r < 6`) to `b' = 8q + c + k`, with `k` in
`{0, 2, 4, 6, 8}`. Hence `3 * b' >= 4 * b - 20`, i.e. `b' - 20 >= (4/3) * (b - 20)`, and
iterating, `b_k - 20 >= (4/3)^k * (b_0 - 20)`. The counter is therefore not merely unbounded:
it grows at least geometrically, at the exact carry rate `8/6 = 4/3` of the Collatz map. The
constant `20` is sharp: at `r = 5`, `c = 0` the step is an equality in `3 * b' >= 4 * b - 20`.
-/

/-- The `b`-counter of an accelerated state. -/
def bOf : State → ℕ
  | .A _ b _ => b

/-- Arithmetic core, truncation-free: `4 b <= 3 b' + 20` for `b' = 8 (b / 6) + c + k`. -/
theorem b_arith_abs (b c k : ℕ) : 4 * b ≤ 3 * (8 * (b / 6) + c + k) + 20 := by
  have h1 : 6 * (b / 6) + b % 6 = b := Nat.div_add_mod b 6
  have h2 : b % 6 < 6 := Nat.mod_lt b (by norm_num)
  omega

/-- One macro step: `3 * b' >= 4 * b - 20`, i.e. `b' >= (4/3) * b - 20/3`. -/
theorem b_step_abs (s s' : State) (h : next s = some s') :
    4 * bOf s ≤ 3 * bOf s' + 20 := by
  obtain ⟨a, b, c⟩ := s
  simp only [next] at h
  split at h
  · rw [Option.some.injEq] at h
    subst h
    exact b_arith_abs b c 0
  · split at h
    · split at h
      · simp at h
      · rw [Option.some.injEq] at h
        subst h
        exact b_arith_abs b c 4
    · split at h
      · rw [Option.some.injEq] at h
        subst h
        exact b_arith_abs b c 2
      · split at h
        · rw [Option.some.injEq] at h
          subst h
          exact b_arith_abs b c 4
        · split at h
          · rw [Option.some.injEq] at h
            subst h
            exact b_arith_abs b c 6
          · rw [Option.some.injEq] at h
            subst h
            exact b_arith_abs b c 8

/-- Offset form: `b' - 20 >= (4/3) * (b - 20)`, the form that iterates cleanly. -/
theorem b_step (s s' : State) (h : next s = some s') :
    4 * (bOf s - 20) ≤ 3 * (bOf s' - 20) := by
  have h1 := b_step_abs s s' h
  omega

/-- Iterated along the orbit: `b_k - 20 >= (4/3)^k * (b_0 - 20)`, in cleared form. -/
theorem b_orbit (n : ℕ) (s0 s : State) (h : runMacro n s0 = some s) :
    4 ^ n * (bOf s0 - 20) ≤ 3 ^ n * (bOf s - 20) := by
  induction n generalizing s0 s with
  | zero =>
    simp only [runMacro, Option.some.injEq] at h
    subst h
    simp
  | succ n ih =>
    change (runMacro n s0).bind next = some s at h
    cases h' : runMacro n s0 with
    | none =>
      rw [h'] at h
      simp at h
    | some mid =>
      rw [h'] at h
      simp only [Option.bind_some] at h
      have h1 : 4 ^ n * (bOf s0 - 20) ≤ 3 ^ n * (bOf mid - 20) := ih s0 mid h'
      have h2 : 4 * (bOf mid - 20) ≤ 3 * (bOf s - 20) := b_step mid s h
      calc
        4 ^ (n + 1) * (bOf s0 - 20)
            = 4 * (4 ^ n * (bOf s0 - 20)) := by rw [pow_succ', Nat.mul_assoc]
        _ ≤ 4 * (3 ^ n * (bOf mid - 20)) := Nat.mul_le_mul_left 4 h1
        _ = 3 ^ n * (4 * (bOf mid - 20)) := by rw [Nat.mul_left_comm]
        _ ≤ 3 ^ n * (3 * (bOf s - 20)) := Nat.mul_le_mul_left _ h2
        _ = 3 ^ (n + 1) * (bOf s - 20) := by rw [pow_succ, ← Nat.mul_assoc]

/-- Explicitly: from `A(4, 65, 1)` (reached in ten macro steps), `3^k * (b_k - 20) >= 45 * 4^k`. -/
theorem b_lower (k : ℕ) (s : State) (h : runMacro k (.A 4 65 1) = some s) :
    4 ^ k * 45 ≤ 3 ^ k * (bOf s - 20) := by
  have h0 := b_orbit k (.A 4 65 1) s h
  have hb : bOf (.A 4 65 1) - 20 = 45 := by decide
  rwa [hb] at h0


/-! ## Parity of the counters

Each rule sends `b = 6q + r` to `b' = 8q + c + k` with `k` even, so `b' ≡ c (mod 2)`; and the new
`c` is odd exactly for the even residues `r ∈ {0, 2, 4}`. Hence `b'' ≡ 1 - b (mod 2)`, and from
`(b, c) = (0, 0)` the pair of parities cycles with period four:

`(0,0) -> (0,1) -> (1,1) -> (1,0) -> (0,0)`.

This is the paper lemma of `bbwork/bigfoot_a_ge_3.md`, section 8.1, kernel-checked.
-/

/-- The `c`-counter of an accelerated state. -/
def cOf : State → ℕ
  | .A _ _ c => c

/-- One macro step: `b' ≡ c (mod 2)` and `c' ≡ 1 - b (mod 2)`. -/
theorem parity_step (s s' : State) (h : next s = some s') :
    bOf s' % 2 = cOf s % 2 ∧ cOf s' % 2 = 1 - bOf s % 2 := by
  obtain ⟨a, b, c⟩ := s
  simp only [next] at h
  split_ifs at h
  · rw [Option.some.injEq] at h
    subst h
    simp only [bOf, cOf]
    constructor <;> omega
  · split at h
    · simp at h
    · rw [Option.some.injEq] at h
      subst h
      simp only [bOf, cOf]
      constructor <;> omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [bOf, cOf]
    constructor <;> omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [bOf, cOf]
    constructor <;> omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [bOf, cOf]
    constructor <;> omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [bOf, cOf]
    constructor <;> omega

/-- Arithmetic shift of the period-four phase. -/
private theorem parity_shift (k : ℕ) : 1 - (k % 4) / 2 = ((k + 2) % 4) / 2 := by
  omega

/-- The parities of `b` and `c` cycle with period four along the orbit: `b` is even exactly when
`k ≡ 0, 1 (mod 4)`, and `c` is odd exactly when `k ≡ 1, 2 (mod 4)`. -/
theorem parity_orbit (k : ℕ) (s : State) (h : runMacro k start = some s) :
    bOf s % 2 = (k % 4) / 2 ∧ cOf s % 2 = ((k + 1) % 4) / 2 := by
  induction k generalizing s with
  | zero =>
    simp only [runMacro, Option.some.injEq] at h
    subst h
    simp [bOf, cOf, start]
  | succ k ih =>
    change (runMacro k start).bind next = some s at h
    cases h' : runMacro k start with
    | none =>
      rw [h'] at h
      simp at h
    | some mid =>
      rw [h'] at h
      simp only [Option.bind_some] at h
      obtain ⟨hb, hc⟩ := ih mid h'
      obtain ⟨hb', hc'⟩ := parity_step mid s h
      constructor
      · rw [hb', hc]
      · rw [hc', hb]
        simpa only [Nat.add_assoc] using parity_shift k

/-- `b` is even exactly at the phases `k ≡ 0, 1 (mod 4)`. -/
theorem b_parity_orbit (k : ℕ) (s : State) (h : runMacro k start = some s) :
    bOf s % 2 = (k % 4) / 2 :=
  (parity_orbit k s h).1

/-- `c` is odd exactly at the phases `k ≡ 1, 2 (mod 4)`. -/
theorem c_parity_orbit (k : ℕ) (s : State) (h : runMacro k start = some s) :
    cOf s % 2 = ((k + 1) % 4) / 2 :=
  (parity_orbit k s h).2

/-! ## Four-step block decomposition of the `a`-counter

Over any four consecutive macro steps the change in `a` is `E + O - D`, where `E` counts the steps
with residue `0`, `O` the steps with residue `3`, and `D` the steps with residue `1`. The balanced
form `a4 + D = a0 + E + O` avoids subtraction; this is the block lemma of
`bbwork/bigfoot_a_ge_3.md`, section 8.2, kernel-checked.
-/

/-- The `a`-counter of an accelerated state. -/
def aOf : State → ℕ
  | .A a _ _ => a

/-- One macro step, balanced form: `a' + [r = 1] = a + [r = 0] + [r = 3]`. -/
theorem a_step (s s' : State) (h : next s = some s') :
    aOf s' + (if bOf s % 6 = 1 then 1 else 0) =
      aOf s + (if bOf s % 6 = 0 then 1 else 0) + (if bOf s % 6 = 3 then 1 else 0) := by
  obtain ⟨a, b, c⟩ := s
  simp only [next] at h
  split_ifs at h
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf, bOf]
    simp_all
  · split at h
    · simp at h
    · rw [Option.some.injEq] at h
      subst h
      simp only [aOf, bOf]
      simp_all
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf, bOf]
    simp_all
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf, bOf]
    simp_all
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf, bOf]
    simp_all
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf, bOf]
    simp_all

/-- Number of `r = 0` steps in a four-step block. -/
def blockE (s0 s1 s2 s3 : State) : ℕ :=
  (if bOf s0 % 6 = 0 then 1 else 0) + (if bOf s1 % 6 = 0 then 1 else 0) +
  (if bOf s2 % 6 = 0 then 1 else 0) + (if bOf s3 % 6 = 0 then 1 else 0)

/-- Number of `r = 3` steps in a four-step block. -/
def blockO (s0 s1 s2 s3 : State) : ℕ :=
  (if bOf s0 % 6 = 3 then 1 else 0) + (if bOf s1 % 6 = 3 then 1 else 0) +
  (if bOf s2 % 6 = 3 then 1 else 0) + (if bOf s3 % 6 = 3 then 1 else 0)

/-- Number of `r = 1` steps in a four-step block. -/
def blockD (s0 s1 s2 s3 : State) : ℕ :=
  (if bOf s0 % 6 = 1 then 1 else 0) + (if bOf s1 % 6 = 1 then 1 else 0) +
  (if bOf s2 % 6 = 1 then 1 else 0) + (if bOf s3 % 6 = 1 then 1 else 0)

/-- Four-step block decomposition: `a4 + D = a0 + E + O`. -/
theorem block4_delta (s0 s1 s2 s3 s4 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2)
    (h2 : next s2 = some s3) (h3 : next s3 = some s4) :
    aOf s4 + blockD s0 s1 s2 s3 = aOf s0 + blockE s0 s1 s2 s3 + blockO s0 s1 s2 s3 := by
  have h0' := a_step s0 s1 h0
  have h1' := a_step s1 s2 h1
  have h2' := a_step s2 s3 h2
  have h3' := a_step s3 s4 h3
  simp only [blockE, blockO, blockD]
  omega

/-- Integer form: `Delta a = E + O - D` over four steps. -/
theorem block4_delta_int (s0 s1 s2 s3 s4 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2)
    (h2 : next s2 = some s3) (h3 : next s3 = some s4) :
    (aOf s4 : ℤ) - (aOf s0 : ℤ) =
      (blockE s0 s1 s2 s3 : ℤ) + (blockO s0 s1 s2 s3 : ℤ) - (blockD s0 s1 s2 s3 : ℤ) := by
  have h := block4_delta s0 s1 s2 s3 s4 h0 h1 h2 h3
  have h' : (aOf s4 : ℤ) + (blockD s0 s1 s2 s3 : ℤ) =
      (aOf s0 : ℤ) + (blockE s0 s1 s2 s3 : ℤ) + (blockO s0 s1 s2 s3 : ℤ) := by
    exact_mod_cast h
  omega

/-! ## Bounds on the four-step change of the `a`-counter

The parity lemma gives exactly two even-`b` and two odd-`b` states among the four pre-step states
of any four consecutive macro steps. An even `b` has residue `0`, `2`, or `4`, so at most two of the
steps are increments (`E`); an odd `b` has residue `1`, `3`, or `5`, and residues `1` and `3` are
mutually exclusive, so `O + D <= 2`. The block identity `Delta a = E + O - D` then gives
`-2 <= Delta a <= 4`.
-/

private theorem mod6_zero_even (b : ℕ) (h : b % 6 = 0) : b % 2 = 0 := by
  omega

private theorem mod6_one_odd (b : ℕ) (h : b % 6 = 1) : b % 2 = 1 := by
  omega

private theorem mod6_three_odd (b : ℕ) (h : b % 6 = 3) : b % 2 = 1 := by
  omega

private theorem ind_zero_le_even (b : ℕ) :
    (if b % 6 = 0 then 1 else 0) ≤ (if b % 2 = 0 then 1 else 0) := by
  by_cases h : b % 6 = 0
  · simp [h, mod6_zero_even b h]
  · simp [h]

private theorem ind_three_add_one_le_odd (b : ℕ) :
    (if b % 6 = 3 then 1 else 0) + (if b % 6 = 1 then 1 else 0) ≤
      (if b % 2 = 1 then 1 else 0) := by
  by_cases h3 : b % 6 = 3
  · simp [h3, mod6_three_odd b h3]
  · by_cases h1 : b % 6 = 1
    · simp [h1, mod6_one_odd b h1]
    · simp [h3, h1]

private def blockEven (s0 s1 s2 s3 : State) : ℕ :=
  (if bOf s0 % 2 = 0 then 1 else 0) + (if bOf s1 % 2 = 0 then 1 else 0) +
  (if bOf s2 % 2 = 0 then 1 else 0) + (if bOf s3 % 2 = 0 then 1 else 0)

private def blockOdd (s0 s1 s2 s3 : State) : ℕ :=
  (if bOf s0 % 2 = 1 then 1 else 0) + (if bOf s1 % 2 = 1 then 1 else 0) +
  (if bOf s2 % 2 = 1 then 1 else 0) + (if bOf s3 % 2 = 1 then 1 else 0)

private theorem ind_zero_eq_one_sub (p : ℕ) (hp : p < 2) :
    (if p = 0 then 1 else 0) = 1 - p := by
  interval_cases p <;> rfl

private theorem ind_one_eq (p : ℕ) (hp : p < 2) :
    (if p = 1 then 1 else 0) = p := by
  interval_cases p <;> rfl

private theorem blockEven_eq_two (s0 s1 s2 s3 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2) (h2 : next s2 = some s3) :
    blockEven s0 s1 s2 s3 = 2 := by
  obtain ⟨hp01, hq01⟩ := parity_step s0 s1 h0
  obtain ⟨hp12, hq12⟩ := parity_step s1 s2 h1
  obtain ⟨hp23, hq23⟩ := parity_step s2 s3 h2
  have h1p : bOf s1 % 2 = cOf s0 % 2 := hp01
  have h2p : bOf s2 % 2 = 1 - bOf s0 % 2 := by rw [hp12, hq01]
  have h3p : bOf s3 % 2 = 1 - bOf s1 % 2 := by rw [hp23, hq12]
  have hb0 : bOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc0 : cOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  simp only [blockEven]
  rw [h3p, h1p, h2p]
  rw [ind_zero_eq_one_sub _ hb0, ind_zero_eq_one_sub _ hc0,
    ind_zero_eq_one_sub _ (by omega), ind_zero_eq_one_sub _ (by omega)]
  omega

private theorem blockOdd_eq_two (s0 s1 s2 s3 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2) (h2 : next s2 = some s3) :
    blockOdd s0 s1 s2 s3 = 2 := by
  obtain ⟨hp01, hq01⟩ := parity_step s0 s1 h0
  obtain ⟨hp12, hq12⟩ := parity_step s1 s2 h1
  obtain ⟨hp23, hq23⟩ := parity_step s2 s3 h2
  have h1p : bOf s1 % 2 = cOf s0 % 2 := hp01
  have h2p : bOf s2 % 2 = 1 - bOf s0 % 2 := by rw [hp12, hq01]
  have h3p : bOf s3 % 2 = 1 - bOf s1 % 2 := by rw [hp23, hq12]
  have hb0 : bOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc0 : cOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  simp only [blockOdd]
  rw [h3p, h1p, h2p]
  rw [ind_one_eq _ hb0, ind_one_eq _ hc0,
    ind_one_eq _ (by omega), ind_one_eq _ (by omega)]
  omega

private theorem blockE_le_blockEven (s0 s1 s2 s3 : State) :
    blockE s0 s1 s2 s3 ≤ blockEven s0 s1 s2 s3 := by
  have h0 := ind_zero_le_even (bOf s0)
  have h1 := ind_zero_le_even (bOf s1)
  have h2 := ind_zero_le_even (bOf s2)
  have h3 := ind_zero_le_even (bOf s3)
  simp only [blockE, blockEven]
  omega

private theorem blockO_add_blockD_le_blockOdd (s0 s1 s2 s3 : State) :
    blockO s0 s1 s2 s3 + blockD s0 s1 s2 s3 ≤ blockOdd s0 s1 s2 s3 := by
  have h0 := ind_three_add_one_le_odd (bOf s0)
  have h1 := ind_three_add_one_le_odd (bOf s1)
  have h2 := ind_three_add_one_le_odd (bOf s2)
  have h3 := ind_three_add_one_le_odd (bOf s3)
  simp only [blockO, blockD, blockOdd]
  omega

/-- Natural-number form of the four-step bound: `a` rises by at most `4` and falls by at most
`2` over any four consecutive macro steps. -/
theorem block4_bounds (s0 s1 s2 s3 s4 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2)
    (h2 : next s2 = some s3) (h3 : next s3 = some s4) :
    aOf s4 ≤ aOf s0 + 4 ∧ aOf s0 ≤ aOf s4 + 2 := by
  have hdelta := block4_delta s0 s1 s2 s3 s4 h0 h1 h2 h3
  have hE := blockE_le_blockEven s0 s1 s2 s3
  have hOD := blockO_add_blockD_le_blockOdd s0 s1 s2 s3
  have hEven := blockEven_eq_two s0 s1 s2 s3 h0 h1 h2
  have hOdd := blockOdd_eq_two s0 s1 s2 s3 h0 h1 h2
  constructor <;> omega

/-- Integer form of the four-step bound: `-2 <= Delta a <= 4`. -/
theorem block4_bounds_int (s0 s1 s2 s3 s4 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2)
    (h2 : next s2 = some s3) (h3 : next s3 = some s4) :
    -(2 : ℤ) ≤ (aOf s4 : ℤ) - (aOf s0 : ℤ) ∧
      (aOf s4 : ℤ) - (aOf s0 : ℤ) ≤ 4 := by
  have h := block4_bounds s0 s1 s2 s3 s4 h0 h1 h2 h3
  constructor
  · have h' : (aOf s0 : ℤ) ≤ (aOf s4 : ℤ) + 2 := by exact_mod_cast h.2
    omega
  · have h' : (aOf s4 : ℤ) ≤ (aOf s0 : ℤ) + 4 := by exact_mod_cast h.1
    omega

/-- The lower endpoint of the four-step bound is attained. The legal run
`A(2,1,6) -> A(1,10,0) -> A(1,14,1) -> A(1,19,3) -> A(0,31,0)` decrements `a` at the first and
last steps and leaves it unchanged in between, so `aOf s0 = aOf s4 + 2`. -/
theorem block4_lower_attained :
    next (.A 2 1 6) = some (.A 1 10 0) ∧
    next (.A 1 10 0) = some (.A 1 14 1) ∧
    next (.A 1 14 1) = some (.A 1 19 3) ∧
    next (.A 1 19 3) = some (.A 0 31 0) ∧
    aOf (.A 2 1 6) = aOf (.A 1 10 0) + 1 ∧
    aOf (.A 1 10 0) = aOf (.A 1 14 1) ∧
    aOf (.A 1 14 1) = aOf (.A 1 19 3) ∧
    aOf (.A 1 19 3) = aOf (.A 0 31 0) + 1 ∧
    aOf (.A 2 1 6) = aOf (.A 0 31 0) + 2 := by
  refine ⟨by decide, by decide, by decide, by decide,
    by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- The upper endpoint of the four-step bound is attained. The legal run
`A(0,0,24) -> A(1,24,1) -> A(2,33,1) -> A(3,45,0) -> A(4,60,0)` increments `a` at every step,
so `aOf s4 = aOf s0 + 4`. -/
theorem block4_upper_attained :
    next (.A 0 0 24) = some (.A 1 24 1) ∧
    next (.A 1 24 1) = some (.A 2 33 1) ∧
    next (.A 2 33 1) = some (.A 3 45 0) ∧
    next (.A 3 45 0) = some (.A 4 60 0) ∧
    aOf (.A 1 24 1) = aOf (.A 0 0 24) + 1 ∧
    aOf (.A 2 33 1) = aOf (.A 1 24 1) + 1 ∧
    aOf (.A 3 45 0) = aOf (.A 2 33 1) + 1 ∧
    aOf (.A 4 60 0) = aOf (.A 3 45 0) + 1 ∧
    aOf (.A 4 60 0) = aOf (.A 0 0 24) + 4 := by
  refine ⟨by decide, by decide, by decide, by decide,
    by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-! ## Cumulative drift of the `a`-counter

Summing the four-step bound over complete blocks and the one-step bound over the remaining
`n % 4` steps gives, for `runMacro n s0 = some s`,
`a(s) <= a(s0) + n` and `a(s0) <= a(s) + 2 * (n / 4) + min (n % 4) 2`.
-/

/-- Composition of macro runs: running `m` steps and then `n` more is `runMacro (m + n)`. -/
theorem runMacro_add (m n : ℕ) (s : State) :
    runMacro (m + n) s = (runMacro m s).bind (runMacro n) := by
  induction n with
  | zero =>
      simp [runMacro]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [runMacro]
      rw [ih, Option.bind_assoc]

private theorem a_step_bound (s s' : State) (h : next s = some s') :
    aOf s' ≤ aOf s + 1 ∧ aOf s ≤ aOf s' + 1 := by
  obtain ⟨a, b, c⟩ := s
  simp only [next] at h
  split_ifs at h
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf]
    omega
  · split at h
    · simp at h
    · rw [Option.some.injEq] at h
      subst h
      simp only [aOf]
      omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf]
    omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf]
    omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf]
    omega
  · rw [Option.some.injEq] at h
    subst h
    simp only [aOf]
    omega

private theorem runMacro_steps_bounds (n : ℕ) (s0 s : State)
    (h : runMacro n s0 = some s) :
    aOf s ≤ aOf s0 + n ∧ aOf s0 ≤ aOf s + n := by
  induction n generalizing s0 s with
  | zero =>
      simp only [runMacro, Option.some.injEq] at h
      subst h
      simp
  | succ n ih =>
      change (runMacro n s0).bind next = some s at h
      cases h' : runMacro n s0 with
      | none =>
          rw [h'] at h
          simp at h
      | some mid =>
          rw [h'] at h
          simp only [Option.bind_some] at h
          have h1 := ih s0 mid h'
          have h2 := a_step_bound mid s h
          constructor <;> omega

private theorem ind_one_le_odd (b : ℕ) :
    (if b % 6 = 1 then 1 else 0) ≤ (if b % 2 = 1 then 1 else 0) := by
  by_cases h : b % 6 = 1
  · have h2 : b % 2 = 1 := by omega
    simp [h, h2]
  · simp [h]

private theorem three_odd_le_two (s0 s1 s2 : State)
    (h0 : next s0 = some s1) (h1 : next s1 = some s2) :
    (if bOf s0 % 2 = 1 then 1 else 0) +
      (if bOf s1 % 2 = 1 then 1 else 0) +
      (if bOf s2 % 2 = 1 then 1 else 0) ≤ 2 := by
  obtain ⟨hp01, hq01⟩ := parity_step s0 s1 h0
  obtain ⟨hp12, hq12⟩ := parity_step s1 s2 h1
  have h1p : bOf s1 % 2 = cOf s0 % 2 := hp01
  have h2p : bOf s2 % 2 = 1 - bOf s0 % 2 := by rw [hp12, hq01]
  have hb0 : bOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc0 : cOf s0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [h1p, h2p]
  rw [ind_one_eq _ hb0, ind_one_eq _ hc0, ind_one_eq _ (by omega)]
  omega

private theorem runMacro_three_exists (s0 s3 : State) (h : runMacro 3 s0 = some s3) :
    ∃ s1 s2, next s0 = some s1 ∧ next s1 = some s2 ∧ next s2 = some s3 := by
  have h3 : runMacro 3 s0 = (runMacro 1 s0).bind (runMacro 2) := by
    simpa using runMacro_add 1 2 s0
  rw [h3] at h
  change Option.bind (next s0) (runMacro 2) = some s3 at h
  cases hn0 : next s0 with
  | none =>
      rw [hn0] at h
      simp at h
  | some s1 =>
      simp only [hn0] at h
      change runMacro 2 s1 = some s3 at h
      have h2 : runMacro 2 s1 = (runMacro 1 s1).bind (runMacro 1) := by
        simpa using runMacro_add 1 1 s1
      rw [h2] at h
      change Option.bind (next s1) (runMacro 1) = some s3 at h
      cases hn1 : next s1 with
      | none =>
          rw [hn1] at h
          simp at h
      | some s2 =>
          simp only [hn1] at h
          change runMacro 1 s2 = some s3 at h
          have hn2 : next s2 = some s3 := by simpa [runMacro] using h
          exact ⟨s1, s2, rfl, hn1, hn2⟩

private theorem runMacro_three_bounds (s0 s3 : State) (h : runMacro 3 s0 = some s3) :
    aOf s3 ≤ aOf s0 + 3 ∧ aOf s0 ≤ aOf s3 + 2 := by
  obtain ⟨s1, s2, h01, h12, h23⟩ := runMacro_three_exists s0 s3 h
  have h0 := a_step s0 s1 h01
  have h1 := a_step s1 s2 h12
  have h2 := a_step s2 s3 h23
  have hd0 := ind_one_le_odd (bOf s0)
  have hd1 := ind_one_le_odd (bOf s1)
  have hd2 := ind_one_le_odd (bOf s2)
  have hodd := three_odd_le_two s0 s1 s2 h01 h12
  have hD : (if bOf s0 % 6 = 1 then 1 else 0) +
      (if bOf s1 % 6 = 1 then 1 else 0) +
      (if bOf s2 % 6 = 1 then 1 else 0) ≤ 2 := by omega
  constructor
  · have b0 := a_step_bound s0 s1 h01
    have b1 := a_step_bound s1 s2 h12
    have b2 := a_step_bound s2 s3 h23
    omega
  · omega

/-- The sharpened three-step lower bound is attained. The legal run
`A(2,1,9) -> A(1,13,0) -> A(0,20,0) -> A(0,26,3)` has `a = 2, 1, 0, 0`: the first two
steps decrement `a`, the third leaves it unchanged, and `aOf s0 = aOf s3 + 2`. -/
theorem three_step_bound_attained :
    next (.A 2 1 9) = some (.A 1 13 0) ∧
    next (.A 1 13 0) = some (.A 0 20 0) ∧
    next (.A 0 20 0) = some (.A 0 26 3) ∧
    aOf (.A 2 1 9) = aOf (.A 1 13 0) + 1 ∧
    aOf (.A 1 13 0) = aOf (.A 0 20 0) + 1 ∧
    aOf (.A 0 26 3) = aOf (.A 0 20 0) ∧
    aOf (.A 2 1 9) = aOf (.A 0 26 3) + 2 := by
  refine ⟨by decide, by decide, by decide, by rfl, by rfl, by rfl, by rfl⟩

private theorem runMacro_remainder_bounds (r : ℕ) (hr : r < 4) (s0 s : State)
    (h : runMacro r s0 = some s) :
    aOf s ≤ aOf s0 + r ∧ aOf s0 ≤ aOf s + min r 2 := by
  interval_cases r
  · simp only [runMacro, Option.some.injEq] at h
    subst h
    simp
  · have hs := runMacro_steps_bounds 1 s0 s h
    simpa using hs
  · have hs := runMacro_steps_bounds 2 s0 s h
    simpa using hs
  · have hs := runMacro_three_bounds s0 s h
    simpa using hs

private theorem runMacro_four_exists (s0 s4 : State) (h : runMacro 4 s0 = some s4) :
    ∃ s1 s2 s3, next s0 = some s1 ∧ next s1 = some s2 ∧
      next s2 = some s3 ∧ next s3 = some s4 := by
  have h4 : runMacro 4 s0 = (runMacro 1 s0).bind (runMacro 3) := by
    simpa using runMacro_add 1 3 s0
  rw [h4] at h
  change Option.bind (next s0) (runMacro 3) = some s4 at h
  cases hn0 : next s0 with
  | none =>
      rw [hn0] at h
      simp at h
  | some s1 =>
      simp only [hn0] at h
      change runMacro 3 s1 = some s4 at h
      have h3 : runMacro 3 s1 = (runMacro 1 s1).bind (runMacro 2) := by
        simpa using runMacro_add 1 2 s1
      rw [h3] at h
      change Option.bind (next s1) (runMacro 2) = some s4 at h
      cases hn1 : next s1 with
      | none =>
          rw [hn1] at h
          simp at h
      | some s2 =>
          simp only [hn1] at h
          change runMacro 2 s2 = some s4 at h
          have h2 : runMacro 2 s2 = (runMacro 1 s2).bind (runMacro 1) := by
            simpa using runMacro_add 1 1 s2
          rw [h2] at h
          change Option.bind (next s2) (runMacro 1) = some s4 at h
          cases hn2 : next s2 with
          | none =>
              rw [hn2] at h
              simp at h
          | some s3 =>
              simp only [hn2] at h
              change runMacro 1 s3 = some s4 at h
              have hn3 : next s3 = some s4 := by
                simpa [runMacro] using h
              exact ⟨s1, s2, s3, rfl, hn1, hn2, hn3⟩

private theorem runMacro_four_bounds (s0 s4 : State) (h : runMacro 4 s0 = some s4) :
    aOf s4 ≤ aOf s0 + 4 ∧ aOf s0 ≤ aOf s4 + 2 := by
  obtain ⟨s1, s2, s3, h01, h12, h23, h34⟩ := runMacro_four_exists s0 s4 h
  exact block4_bounds s0 s1 s2 s3 s4 h01 h12 h23 h34

private theorem runMacro_bounds_aux (q r : ℕ) (hr : r < 4) (s0 s : State)
    (h : runMacro (4 * q + r) s0 = some s) :
    aOf s ≤ aOf s0 + 4 * q + r ∧
      aOf s0 ≤ aOf s + 2 * q + min r 2 := by
  induction q generalizing s0 s with
  | zero =>
      have h0 : runMacro r s0 = some s := by simpa using h
      have hs := runMacro_remainder_bounds r hr s0 s h0
      omega
  | succ q ih =>
      have hlen : 4 * (q + 1) + r = 4 + (4 * q + r) := by omega
      rw [hlen] at h
      rw [runMacro_add 4 (4 * q + r) s0] at h
      cases h4 : runMacro 4 s0 with
      | none =>
          rw [h4] at h
          simp at h
      | some s1 =>
          rw [h4] at h
          simp only [Option.bind_some] at h
          have h4b := runMacro_four_bounds s0 s1 h4
          have hrec := ih s1 s h
          constructor <;> omega

/-- Cumulative drift bound: after `n` macro steps, `a` has risen by at most `n` and fallen by
at most `2 * (n / 4) + min (n % 4) 2`. -/
theorem runMacro_bounds (n : ℕ) (s0 s : State) (h : runMacro n s0 = some s) :
    aOf s ≤ aOf s0 + n ∧
      aOf s0 ≤ aOf s + 2 * (n / 4) + min (n % 4) 2 := by
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hn : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
  have h' : runMacro (4 * (n / 4) + n % 4) s0 = some s := by
    rw [hn]
    exact h
  have hb := runMacro_bounds_aux (n / 4) (n % 4) hr s0 s h'
  constructor <;> omega

/-- Integer form of the cumulative drift bound:
`-(2 * (n / 4) + n % 4) <= a_n - a_0 <= n`. -/
theorem runMacro_bounds_int (n : ℕ) (s0 s : State) (h : runMacro n s0 = some s) :
    -((2 * (n / 4) + min (n % 4) 2 : ℕ) : ℤ) ≤ (aOf s : ℤ) - (aOf s0 : ℤ) ∧
      (aOf s : ℤ) - (aOf s0 : ℤ) ≤ (n : ℤ) := by
  have hb := runMacro_bounds n s0 s h
  constructor
  · have h' : (aOf s0 : ℤ) ≤ (aOf s : ℤ) + (2 * (n / 4) : ℤ) +
        ((min (n % 4) 2 : ℕ) : ℤ) := by
      exact_mod_cast hb.2
    have hcast : ((2 * (n / 4) + min (n % 4) 2 : ℕ) : ℤ) =
        (2 * (n / 4) : ℤ) + ((min (n % 4) 2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast]
    omega
  · have h' : (aOf s : ℤ) ≤ (aOf s0 : ℤ) + (n : ℤ) := by
      exact_mod_cast hb.1
    omega

/-- The cumulative lower bound is tight at `n = 3`. The three-step witness
`A(2,1,9) -> A(0,26,3)` has `a_0 = a_3 + 2`, so the lower bound from `runMacro_bounds`,
`2 * (3 / 4) + min (3 % 4) 2 = 2`, is attained with equality. -/
theorem runMacro_bounds_three_tight :
    runMacro 3 (.A 2 1 9) = some (.A 0 26 3) ∧
      aOf (.A 2 1 9) ≤ aOf (.A 0 26 3) + 2 * (3 / 4) + min (3 % 4) 2 ∧
      aOf (.A 2 1 9) = aOf (.A 0 26 3) + 2 * (3 / 4) + min (3 % 4) 2 := by
  have hrun : runMacro 3 (.A 2 1 9) = some (.A 0 26 3) := by decide
  have hb := (runMacro_bounds 3 (.A 2 1 9) (.A 0 26 3) hrun).2
  have htight : aOf (.A 2 1 9) = aOf (.A 0 26 3) + 2 :=
    three_step_bound_attained.2.2.2.2.2.2
  refine ⟨hrun, hb, ?_⟩
  simpa using htight

/-- The cumulative upper bound is tight at `n = 4`. The four-step witness
`A(0,0,24) -> A(1,24,1) -> A(2,33,1) -> A(3,45,0) -> A(4,60,0)` increments `a` at every
step, so `a_4 = a_0 + 4` and the upper cumulative bound is attained with equality. -/
theorem runMacro_bounds_four_upper_tight :
    runMacro 4 (.A 0 0 24) = some (.A 4 60 0) ∧
      aOf (.A 4 60 0) ≤ aOf (.A 0 0 24) + 4 ∧
      aOf (.A 4 60 0) = aOf (.A 0 0 24) + 4 := by
  have hrun : runMacro 4 (.A 0 0 24) = some (.A 4 60 0) := by decide
  have hb := (runMacro_bounds 4 (.A 0 0 24) (.A 4 60 0) hrun).1
  have htight : aOf (.A 4 60 0) = aOf (.A 0 0 24) + 4 :=
    block4_upper_attained.2.2.2.2.2.2.2.2
  exact ⟨hrun, hb, htight⟩

/-- The cumulative lower bound is tight at `n = 4`. The four-step witness
`A(2,1,6) -> A(1,10,0) -> A(1,14,1) -> A(1,19,3) -> A(0,31,0)` has
`a = 2 -> 1 -> 1 -> 1 -> 0`, so `a_0 = a_4 + 2` and the lower cumulative bound is
attained with equality. -/
theorem runMacro_bounds_four_lower_tight :
    runMacro 4 (.A 2 1 6) = some (.A 0 31 0) ∧
      aOf (.A 2 1 6) ≤ aOf (.A 0 31 0) + 2 * (4 / 4) + min (4 % 4) 2 ∧
      aOf (.A 2 1 6) = aOf (.A 0 31 0) + 2 * (4 / 4) + min (4 % 4) 2 := by
  have hrun : runMacro 4 (.A 2 1 6) = some (.A 0 31 0) := by decide
  have hb := (runMacro_bounds 4 (.A 2 1 6) (.A 0 31 0) hrun).2
  have htight : aOf (.A 2 1 6) = aOf (.A 0 31 0) + 2 :=
    block4_lower_attained.2.2.2.2.2.2.2.2
  refine ⟨hrun, hb, ?_⟩
  simpa using htight

/-- The cumulative lower bound is tight at `n = 2`. The two-step prefix
`A(2,1,9) -> A(1,13,0) -> A(0,20,0)` of the three-step witness has `a = 2 -> 1 -> 0`,
so `a_0 = a_2 + 2` and the lower bound is attained with equality. -/
theorem runMacro_bounds_two_lower_tight :
    runMacro 2 (.A 2 1 9) = some (.A 0 20 0) ∧
      aOf (.A 2 1 9) ≤ aOf (.A 0 20 0) + 2 * (2 / 4) + min (2 % 4) 2 ∧
      aOf (.A 2 1 9) = aOf (.A 0 20 0) + 2 * (2 / 4) + min (2 % 4) 2 := by
  have hrun : runMacro 2 (.A 2 1 9) = some (.A 0 20 0) := by decide
  have hb := (runMacro_bounds 2 (.A 2 1 9) (.A 0 20 0) hrun).2
  have htight : aOf (.A 2 1 9) = aOf (.A 0 20 0) + 2 := by decide
  refine ⟨hrun, hb, ?_⟩
  simpa using htight

/-- The cumulative lower bound is tight at `n = 5`. The legal run
`A(3,7,1) -> A(2,13,0) -> A(1,20,0) -> A(1,26,3) -> A(1,37,3) -> A(0,55,0)` has
`a = 3 -> 2 -> 1 -> 1 -> 1 -> 0`, so `a_0 = a_5 + 3` and the lower bound is attained with
equality. In particular, five consecutive steps can contain three decrements. -/
theorem runMacro_bounds_five_lower_tight :
    runMacro 5 (.A 3 7 1) = some (.A 0 55 0) ∧
      aOf (.A 3 7 1) ≤ aOf (.A 0 55 0) + 2 * (5 / 4) + min (5 % 4) 2 ∧
      aOf (.A 3 7 1) = aOf (.A 0 55 0) + 2 * (5 / 4) + min (5 % 4) 2 := by
  have hrun : runMacro 5 (.A 3 7 1) = some (.A 0 55 0) := by decide
  have hb := (runMacro_bounds 5 (.A 3 7 1) (.A 0 55 0) hrun).2
  have htight : aOf (.A 3 7 1) = aOf (.A 0 55 0) + 3 := by decide
  refine ⟨hrun, hb, ?_⟩
  simpa using htight


end BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA


