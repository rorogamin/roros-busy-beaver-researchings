import RequestProject.Macro

/-!
# Mixed-radix return excursions

Draft extension to the uploaded project. This file was written without an
available Lean compiler and MUST be compiled before treating it as checked.
It contains no proposed proof of `not Halts`.

A return excursion enters a finite word in A from the left and comes back to
its left neighbour in B. Its behaviour is independent of both outside tapes.
The fundamental rules are:
  F(42 x) = 44 x
  F(44 x) = 42 F(x)
  F(2 x)  = 2 F(F(F(x))).

`MRAdd` batches these rules: a 2 triples the carry, and a binary pair halves it.
`mrAdd_single_sound` is the intended soundness theorem for one accelerated
return. `mrAdd_value` records the associated rational-valued counter.
-/

namespace TM2x5

/-- An exact, context-independent return excursion, with its step count. -/
def ReturnRule (u v : List Sym) (n : Nat) : Prop :=
  forall (a : Sym) (l r : List Sym),
    iter n (some (onFirst St.A (a :: l) (u ++ r))) =
      some (Cfg.mk St.B l a (v ++ r))

theorem return_42 (w : List Sym) :
    ReturnRule ((4 : Sym) :: 2 :: w) ((4 : Sym) :: 4 :: w) 3 := by
  intro a l r
  rfl

theorem return_44 {u v : List Sym} {n : Nat} (h : ReturnRule u v n) :
    ReturnRule ((4 : Sym) :: 4 :: u) ((4 : Sym) :: 2 :: v) (n + 4) := by
  intro a l r
  have hs : iter 2
      (some (onFirst St.A (a :: l) (((4 : Sym) :: 4 :: u) ++ r))) =
      some (onFirst St.A ((0 : Sym) :: 2 :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    cases u ++ r <;> rfl
  have he : iter 2 (some (Cfg.mk St.B ((2 : Sym) :: a :: l) 0 (v ++ r))) =
      some (Cfg.mk St.B l a (((4 : Sym) :: 2 :: v) ++ r)) := rfl
  rw [show n + 4 = 2 + (n + 2) by omega, iter_add, hs, iter_add,
    h 0 ((2 : Sym) :: a :: l) r, he]

theorem return_two_three {u v w z : List Sym} {n1 n2 n3 : Nat}
    (h1 : ReturnRule u v n1) (h2 : ReturnRule v w n2)
    (h3 : ReturnRule w z n3) :
    ReturnRule ((2 : Sym) :: u) ((2 : Sym) :: z) (4 + n1 + n2 + n3) := by
  intro a l r
  have hs : iter 1
      (some (onFirst St.A (a :: l) (((2 : Sym) :: u) ++ r))) =
      some (onFirst St.A ((3 : Sym) :: a :: l) (u ++ r)) := by
    simp only [List.cons_append]
    cases u ++ r <;> rfl
  have h34 : iter 1 (some (Cfg.mk St.B (a :: l) 3 (v ++ r))) =
      some (onFirst St.A ((4 : Sym) :: a :: l) (v ++ r)) := by
    cases v ++ r <;> rfl
  have h40 : iter 1 (some (Cfg.mk St.B (a :: l) 4 (w ++ r))) =
      some (onFirst St.A ((0 : Sym) :: a :: l) (w ++ r)) := by
    cases w ++ r <;> rfl
  have he : iter 1 (some (Cfg.mk St.B (a :: l) 0 (z ++ r))) =
      some (Cfg.mk St.B l a (((2 : Sym) :: z) ++ r)) := rfl
  rw [show 4 + n1 + n2 + n3 =
      1 + (n1 + (1 + (n2 + (1 + (n3 + 1))))) by omega,
    iter_add, hs, iter_add, h1 3 (a :: l) r,
    iter_add, h34, iter_add, h2 4 (a :: l) r,
    iter_add, h40, iter_add, h3 0 (a :: l) r, he]

/-- A virtual sequence of returns; restarting at the right is not counted.
Actual restart steps are included by `return_two_three` when this is lifted
through a cell holding 2. -/
inductive ReturnBatch : Nat -> List Sym -> List Sym -> Nat -> Prop
  | nil (u : List Sym) : ReturnBatch 0 u u 0
  | cons {k : Nat} {u v w : List Sym} {n m : Nat} :
      ReturnRule u v n -> ReturnBatch k v w m -> ReturnBatch (k + 1) u w (n + m)

theorem batch_append {k : Nat} {u v : List Sym} {n : Nat}
    (h1 : ReturnBatch k u v n) :
    forall {j : Nat} {w : List Sym} {m : Nat}, ReturnBatch j v w m ->
      ReturnBatch (k + j) u w (n + m) := by
  induction h1 with
  | nil u =>
    intro j w m h2
    simpa using h2
  | cons hr hb ih =>
    intro j w m h2
    have h := ReturnBatch.cons hr (ih h2)
    convert h using 1 <;> omega

theorem batch_inv {k : Nat} {u v : List Sym} {n : Nat}
    (h : ReturnBatch (k + 1) u v n) :
    ∃ w a b, ReturnRule u w a ∧ ReturnBatch k w v b ∧ n = a + b := by
  cases h with
  | cons hr hb => exact ⟨_, _, _, hr, hb, rfl⟩

theorem batch_two (k : Nat) {u v : List Sym} {n : Nat}
    (h : ReturnBatch (3 * k) u v n) :
    ReturnBatch k ((2 : Sym) :: u) ((2 : Sym) :: v) (4 * k + n) := by
  induction k generalizing u v n with
  | zero =>
    cases h
    exact ReturnBatch.nil _
  | succ k ih =>
    have h0 : ReturnBatch ((3 * k + 2) + 1) u v n := by
      convert h using 1 <;> omega
    obtain ⟨u1, a, b, ha, hb, hn⟩ := batch_inv h0
    have hb' : ReturnBatch ((3 * k + 1) + 1) u1 v b := by
      convert hb using 1 <;> omega
    obtain ⟨u2, c, d, hc, hd, hbd⟩ := batch_inv hb'
    have hd' : ReturnBatch ((3 * k) + 1) u2 v d := by
      convert hd using 1 <;> omega
    obtain ⟨u3, e, f, he, hf, hdf⟩ := batch_inv hd'
    have ht := ReturnBatch.cons (return_two_three ha hc he) (ih hf)
    convert ht using 1 <;> omega

theorem batch_even_zero {k : Nat} {u v : List Sym} {n : Nat}
    (h : ReturnBatch k u v n) :
    ReturnBatch (2 * k) ((4 : Sym) :: 2 :: u) ((4 : Sym) :: 2 :: v) (7 * k + n) := by
  induction h with
  | nil u => exact ReturnBatch.nil _
  | cons hr hb ih =>
    have ht := ReturnBatch.cons (return_42 _) (ReturnBatch.cons (return_44 hr) ih)
    convert ht using 1 <;> omega

theorem batch_even_one {k : Nat} {u v : List Sym} {n : Nat}
    (h : ReturnBatch k u v n) :
    ReturnBatch (2 * k) ((4 : Sym) :: 4 :: u) ((4 : Sym) :: 4 :: v) (7 * k + n) := by
  induction h with
  | nil u => exact ReturnBatch.nil _
  | cons hr hb ih =>
    have ht := ReturnBatch.cons (return_44 hr) (ReturnBatch.cons (return_42 _) ih)
    convert ht using 1 <;> omega

theorem batch_odd_zero {k : Nat} {u v : List Sym} {n : Nat}
    (h : ReturnBatch k u v n) :
    ReturnBatch (2 * k + 1) ((4 : Sym) :: 2 :: u) ((4 : Sym) :: 4 :: v)
      (7 * k + n + 3) := by
  have hlast := ReturnBatch.cons (return_42 v) (ReturnBatch.nil _)
  have ht := batch_append (batch_even_zero h) hlast
  convert ht using 1 <;> omega

theorem batch_odd_one {k : Nat} {u v : List Sym} {n : Nat}
    (h : ReturnBatch (k + 1) u v n) :
    ReturnBatch (2 * k + 1) ((4 : Sym) :: 4 :: u) ((4 : Sym) :: 2 :: v)
      (7 * k + n + 4) := by
  obtain ⟨w, a, b, hr, hb, hn⟩ := batch_inv h
  have ht := ReturnBatch.cons (return_44 hr) (batch_even_zero hb)
  convert ht using 1 <;> omega

inductive MRToken
  | third
  | bit (b : Bool)
  deriving DecidableEq, Repr

def mrBitVal (b : Bool) : Nat := if b then 1 else 0

def mrBitSym (b : Bool) : Sym := if b then 4 else 2

def mrDecode : List MRToken -> List Sym
  | [] => []
  | MRToken.third :: xs => (2 : Sym) :: mrDecode xs
  | MRToken.bit b :: xs => (4 : Sym) :: mrBitSym b :: mrDecode xs

/-- A finite certificate for a successful batched carry. -/
inductive MRAdd : Nat -> List MRToken -> List MRToken -> Nat -> Prop
  | zero (xs : List MRToken) : MRAdd 0 xs xs 0
  | third {k : Nat} {xs ys : List MRToken} {n : Nat} :
      MRAdd (3 * k) xs ys n ->
      MRAdd k (MRToken.third :: xs) (MRToken.third :: ys) (4 * k + n)
  | bit {k q : Nat} {b b' : Bool} {xs ys : List MRToken} {n : Nat} :
      mrBitVal b + k = 2 * q + mrBitVal b' -> MRAdd q xs ys n ->
      MRAdd k (MRToken.bit b :: xs) (MRToken.bit b' :: ys) (3 * k + q + n)

theorem mrAdd_sound {k : Nat} {xs ys : List MRToken} {n : Nat}
    (h : MRAdd k xs ys n) : ReturnBatch k (mrDecode xs) (mrDecode ys) n := by
  induction h with
  | zero xs => exact ReturnBatch.nil _
  | @third k xs ys n h ih =>
    simpa only [mrDecode] using batch_two k ih
  | @bit k q b b' xs ys n he h ih =>
    cases b <;> cases b'
    · have hk : k = 2 * q := by simp [mrBitVal] at he; omega
      subst k
      have ht := batch_even_zero ih
      change ReturnBatch (2 * q) ((4 : Sym) :: 2 :: mrDecode xs)
        ((4 : Sym) :: 2 :: mrDecode ys) (3 * (2 * q) + q + n)
      convert ht using 1 <;> omega
    · have hk : k = 2 * q + 1 := by simp [mrBitVal] at he; omega
      subst k
      have ht := batch_odd_zero ih
      change ReturnBatch (2 * q + 1) ((4 : Sym) :: 2 :: mrDecode xs)
        ((4 : Sym) :: 4 :: mrDecode ys) (3 * (2 * q + 1) + q + n)
      convert ht using 1 <;> omega
    · have hq : 0 < q := by simp [mrBitVal] at he; omega
      cases q with
      | zero => omega
      | succ q =>
        have hk : k = 2 * q + 1 := by simp [mrBitVal] at he; omega
        subst k
        have ht := batch_odd_one ih
        change ReturnBatch (2 * q + 1) ((4 : Sym) :: 4 :: mrDecode xs)
          ((4 : Sym) :: 2 :: mrDecode ys) (3 * (2 * q + 1) + (q + 1) + n)
        convert ht using 1 <;> omega
    · have hk : k = 2 * q := by simp [mrBitVal] at he; omega
      subst k
      have ht := batch_even_one ih
      change ReturnBatch (2 * q) ((4 : Sym) :: 4 :: mrDecode xs)
        ((4 : Sym) :: 4 :: mrDecode ys) (3 * (2 * q) + q + n)
      convert ht using 1 <;> omega

/-- Every successful single-carry certificate is an exact TM return. -/
theorem mrAdd_single_sound {xs ys : List MRToken} {n : Nat}
    (h : MRAdd 1 xs ys n) : ReturnRule (mrDecode xs) (mrDecode ys) n := by
  obtain ⟨w, a, b, hr, hb, hn⟩ := batch_inv (mrAdd_sound h)
  cases hb
  simp only [Nat.add_zero] at hn
  subst n
  exact hr

/-- The mixed-radix value is rational because a `third` divides by 3. -/
def mrValue : List MRToken -> Rat
  | [] => 0
  | MRToken.third :: xs => mrValue xs / 3
  | MRToken.bit b :: xs => 2 * mrValue xs + mrBitVal b

theorem mrAdd_value {k : Nat} {xs ys : List MRToken} {n : Nat}
    (h : MRAdd k xs ys n) : mrValue ys = mrValue xs + k := by
  induction h with
  | zero xs => simp
  | @third k xs ys n h ih =>
    simp only [mrValue]
    rw [ih]
    push_cast
    ring
  | @bit k q b b' xs ys n he h ih =>
    have he' : (mrBitVal b : Rat) + (k : Rat) =
        2 * (q : Rat) + (mrBitVal b' : Rat) := by exact_mod_cast he
    simp only [mrValue]
    rw [ih]
    linarith

end TM2x5
