module

public import RequestProject.Machine

/-!
# Finite longitudinal rectangles

This file formalises the combinatorial core of the "finite-rectangle" nonhalting argument for
`1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`.

A *letter* records one visit of the head to a region entered from its right: the state in
which the head enters, and the state in which it eventually leaves again to the right.  Only
the three letters `a = (A,B)`, `b = (B,B)`, `c = (A,A)` are needed.

* `Visit s X M Y t` : a cell holding `s`, entered from the right in state `X`, makes the
  excursions `M` to its left neighbour (each letter = departure state, return state) and
  finally leaves to the right in state `Y`, holding `t`.  Every transition used is one of the
  nine non-halting transitions of the machine (`tr`).
* `Cell s R L t` : a finite sequence of such visits (right boundary word `R`, left boundary
  word `L`).
* `Rect S R L T` : a list of neighbouring cells (ordered **right to left**) with matching
  shared boundary words.

Everything in this file is purely about words; the connection with the actual machine is in
`RequestProject/Oracle.lean`.
-/

@[expose] public section

namespace BB25
namespace LR

/-- The three boundary letters. -/
inductive Letter
  | a
  | b
  | c
  deriving DecidableEq, Repr

open Letter

/-- Entry state of a letter. -/
def Letter.ent : Letter → St
  | .a => .A
  | .b => .B
  | .c => .A

/-- Exit state of a letter. -/
def Letter.ext : Letter → St
  | .a => .B
  | .b => .B
  | .c => .A

/-- The non-halting part of the transition table: `some (written symbol, moves right?, next
state)`.  `A` reading `4` (the halting transition) and the state `H` give `none`. -/
def tr (X : St) (s : Sym) : Option (Sym × Bool × St) :=
  match X, s.val with
  | .A, 0 => some (1, true, .B)
  | .A, 1 => some (2, false, .A)
  | .A, 2 => some (3, false, .B)
  | .A, 3 => some (4, false, .B)
  | .B, 0 => some (0, false, .A)
  | .B, 1 => some (4, false, .B)
  | .B, 2 => some (3, true, .A)
  | .B, 3 => some (4, false, .A)
  | .B, 4 => some (0, true, .B)
  | _, _ => none

/-- One visit of a single cell. -/
inductive Visit : Sym → St → List Letter → St → Sym → Prop
  | right {s : Sym} {X : St} {w : Sym} {Y : St} :
      tr X s = some (w, true, Y) → Visit s X [] Y w
  | left {s : Sym} {X : St} {w : Sym} {M : List Letter} {Y : St} {t : Sym} (m : Letter) :
      tr X s = some (w, false, m.ent) → Visit w m.ext M Y t → Visit s X (m :: M) Y t

/-- A finite history of a single cell. -/
inductive Cell : Sym → List Letter → List Letter → Sym → Prop
  | nil (s : Sym) : Cell s [] [] s
  | cons {s : Sym} {r : Letter} {M1 : List Letter} {s1 : Sym} {R M2 : List Letter} {t : Sym} :
      Visit s r.ent M1 r.ext s1 → Cell s1 R M2 t → Cell s (r :: R) (M1 ++ M2) t

/-- A finite rectangle: cells listed from right to left, with matching shared boundaries. -/
inductive Rect : List Sym → List Letter → List Letter → List Sym → Prop
  | nil (R : List Letter) : Rect [] R R []
  | cons {s : Sym} {R M : List Letter} {t : Sym} {S : List Sym} {L : List Letter}
      {T : List Sym} : Cell s R M t → Rect S M L T → Rect (s :: S) R L (t :: T)

/-! ### Composition lemmas -/

theorem Cell.single {s : Sym} {r : Letter} {L : List Letter} {t : Sym}
    (h : Visit s r.ent L r.ext t) : Cell s [r] L t := by
  simpa using Cell.cons h (Cell.nil t)

theorem Cell.append {s t u : Sym} {R1 L1 R2 L2 : List Letter}
    (h1 : Cell s R1 L1 t) (h2 : Cell t R2 L2 u) : Cell s (R1 ++ R2) (L1 ++ L2) u := by
  induction h1 with
  | nil => simpa using h2
  | cons hv _ ih => simpa [List.append_assoc] using Cell.cons hv (ih h2)

theorem Cell.split {s u : Sym} {R1 R2 L : List Letter} (h : Cell s (R1 ++ R2) L u) :
    ∃ L1 L2 t, L = L1 ++ L2 ∧ Cell s R1 L1 t ∧ Cell t R2 L2 u := by
  induction R1 generalizing s L with
  | nil => exact ⟨[], L, s, rfl, Cell.nil s, by simpa using h⟩
  | cons r R1 ih =>
    cases h with
    | cons hv hc =>
      obtain ⟨L1, L2, t, rfl, h1, h2⟩ := ih hc
      exact ⟨_ ++ L1, L2, t, by simp, Cell.cons hv h1, h2⟩

theorem Rect.length_eq {S T : List Sym} {R L : List Letter} (h : Rect S R L T) :
    T.length = S.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Rect.cast {S S' T T' : List Sym} {R R' L L' : List Letter} (h : Rect S R L T)
    (hS : S = S') (hR : R = R') (hL : L = L') (hT : T = T') : Rect S' R' L' T' := by
  subst hS hR hL hT; exact h

/-- Temporal composition. -/
theorem Rect.append {S T U : List Sym} {R1 L1 R2 L2 : List Letter}
    (h1 : Rect S R1 L1 T) (h2 : Rect T R2 L2 U) : Rect S (R1 ++ R2) (L1 ++ L2) U := by
  induction h1 generalizing R2 L2 U with
  | nil => cases h2; exact Rect.nil _
  | cons hc _ ih =>
    cases h2 with
    | cons hc2 hr2 => exact Rect.cons (hc.append hc2) (ih hr2)

/-- Temporal splitting. -/
theorem Rect.split {S U : List Sym} {R1 R2 L : List Letter} (h : Rect S (R1 ++ R2) L U) :
    ∃ L1 L2 T, L = L1 ++ L2 ∧ Rect S R1 L1 T ∧ Rect T R2 L2 U := by
  induction S generalizing R1 R2 L U with
  | nil => cases h; exact ⟨R1, R2, [], rfl, Rect.nil _, Rect.nil _⟩
  | cons s S ih =>
    cases h with
    | cons hc hr =>
      obtain ⟨M1, M2, t, rfl, h1, h2⟩ := hc.split
      obtain ⟨L1, L2, T, rfl, h3, h4⟩ := ih hr
      exact ⟨L1, L2, t :: T, rfl, Rect.cons h1 h3, Rect.cons h2 h4⟩

/-- Spatial composition. -/
theorem Rect.space {S S' T T' : List Sym} {R M L : List Letter}
    (h1 : Rect S R M S') (h2 : Rect T M L T') : Rect (S ++ T) R L (S' ++ T') := by
  induction h1 with
  | nil => simpa using h2
  | cons hc _ ih => exact Rect.cons hc (ih h2)

/-- Spatial cutting. -/
theorem Rect.cut {S1 S2 U : List Sym} {R L : List Letter} (h : Rect (S1 ++ S2) R L U) :
    ∃ M U1 U2, U = U1 ++ U2 ∧ U1.length = S1.length ∧ Rect S1 R M U1 ∧ Rect S2 M L U2 := by
  induction S1 generalizing R U with
  | nil => exact ⟨R, [], U, rfl, rfl, Rect.nil _, by simpa using h⟩
  | cons s S1 ih =>
    cases h with
    | cons hc hr =>
      obtain ⟨M', U1, U2, rfl, hl, h1, h2⟩ := ih hr
      exact ⟨M', _ :: U1, U2, rfl, by simp [hl], Rect.cons hc h1, h2⟩

theorem Rect.one {s t : Sym} {R L : List Letter} (h : Cell s R L t) : Rect [s] R L [t] :=
  Rect.cons h (Rect.nil L)

/-! ### Words -/

theorem rep_add {α : Type} (m n : Nat) (x : α) :
    List.replicate (m + n) x = List.replicate m x ++ List.replicate n x :=
  List.replicate_append_replicate.symm

/-- `pw w n` is the word `w` repeated `n` times. -/
def pw (w : List Letter) : Nat → List Letter
  | 0 => []
  | n + 1 => w ++ pw w n

@[simp] theorem pw_zero (w : List Letter) : pw w 0 = [] := rfl

theorem pw_succ (w : List Letter) (n : Nat) : pw w (n + 1) = w ++ pw w n := rfl

theorem pw_succ' (w : List Letter) (n : Nat) : pw w (n + 1) = pw w n ++ w := by
  induction n with
  | zero => simp [pw]
  | succ n ih =>
    calc pw w (n + 1 + 1) = w ++ pw w (n + 1) := rfl
      _ = w ++ (pw w n ++ w) := by rw [ih]
      _ = pw w (n + 1) ++ w := by rw [pw_succ, List.append_assoc]

/-- The conjugation identity `x (y x)^n = (x y)^n x`. -/
theorem pw_conj (x y : List Letter) (n : Nat) : x ++ pw (y ++ x) n = pw (x ++ y) n ++ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ++ pw (y ++ x) (n + 1) = (x ++ y) ++ (x ++ pw (y ++ x) n) := by
          rw [pw_succ]; simp only [List.append_assoc]
      _ = (x ++ y) ++ (pw (x ++ y) n ++ x) := by rw [ih]
      _ = pw (x ++ y) (n + 1) ++ x := by rw [pw_succ]; simp only [List.append_assoc]

/-- `a^k`. -/
abbrev A (k : Nat) : List Letter := List.replicate k a

/-- The three period words `D = cab`, `E = cba`, `F = bca`. -/
def D : List Letter := [c, a, b]
def E : List Letter := [c, b, a]
def F : List Letter := [b, c, a]

theorem A_add (m n : Nat) : A (m + n) = A m ++ A n := rep_add _ _ _

theorem A_succ (n : Nat) : A (n + 1) = a :: A n := rfl

/-! ### Single-cell table -/

theorem cell0a : Cell 0 [a] [] 1 := Cell.single (Visit.right rfl)

theorem visit0b (k : Nat) : Visit 0 .B (A k ++ [c]) .B 1 := by
  induction k with
  | zero => exact Visit.left c rfl (Visit.right rfl)
  | succ k ih => exact Visit.left a rfl ih

theorem cell0b (k : Nat) : Cell 0 [b] (A k ++ [c]) 1 := Cell.single (visit0b k)

theorem cell1a : Cell 1 [a] [c, b, a] 0 :=
  Cell.single (Visit.left c rfl (Visit.left b rfl (Visit.left a rfl (Visit.right rfl))))

theorem cell1b : Cell 1 [b] [b] 0 := Cell.single (Visit.left b rfl (Visit.right rfl))

theorem cell1c : Cell 1 [c] [a] 3 := Cell.single (Visit.left a rfl (Visit.right rfl))

theorem cell3a : Cell 3 [a] [b] 0 := Cell.single (Visit.left b rfl (Visit.right rfl))

theorem cell3b : Cell 3 [b] [a] 0 := Cell.single (Visit.left a rfl (Visit.right rfl))

/-! ### Derived single-cell histories -/

theorem cell1aa : Cell 1 [a, a] E 1 := by
  simpa [E] using cell1a.append cell0a

theorem cell1E : Cell 1 E [a, a] 1 := by
  simpa [E] using (cell1c.append cell3b).append cell0a

theorem cell1D (k : Nat) : Cell 1 D ([a, b] ++ A k ++ [c]) 1 := by
  simpa [D] using (cell1c.append cell3a).append (cell0b k)

theorem cell0F : Cell 0 F D 0 := by
  simpa [F, D] using ((cell0b 0).append cell1c).append cell3a

theorem cell0ab : Cell 0 [a, b] [b] 0 := by
  simpa using cell0a.append cell1b

theorem cell1_A2 (j : Nat) : Cell 1 (A (2 * j)) (pw E j) 1 := by
  induction j with
  | zero => exact Cell.nil 1
  | succ j ih =>
    have : A (2 * (j + 1)) = [a, a] ++ A (2 * j) := by
      rw [show 2 * (j + 1) = 2 + 2 * j by omega, A_add]; rfl
    rw [this, pw_succ]
    exact cell1aa.append ih

theorem cell1_E (j : Nat) : Cell 1 (pw E j) (A (2 * j)) 1 := by
  induction j with
  | zero => exact Cell.nil 1
  | succ j ih =>
    have : A (2 * (j + 1)) = [a, a] ++ A (2 * j) := by
      rw [show 2 * (j + 1) = 2 + 2 * j by omega, A_add]; rfl
    rw [this, pw_succ]
    exact cell1E.append ih

theorem cell1_D0 (m : Nat) : Cell 1 (pw D m) (pw [a, b, c] m) 1 := by
  induction m with
  | zero => exact Cell.nil 1
  | succ m ih =>
    rw [pw_succ, pw_succ]
    simpa using (cell1D 0).append ih

theorem cell0_F (m : Nat) : Cell 0 (pw F m) (pw D m) 0 := by
  induction m with
  | zero => exact Cell.nil 0
  | succ m ih => rw [pw_succ, pw_succ]; exact cell0F.append ih

theorem cell0_odd (q : Nat) : Cell 0 (A (2 * q + 1)) (pw E q) 1 := by
  rw [show 2 * q + 1 = 1 + 2 * q by omega, A_add]
  simpa using cell0a.append (cell1_A2 q)

/-- `c (abc)^m = (cab)^m c`. -/
theorem c_abc (m : Nat) : [c] ++ pw [a, b, c] m = pw D m ++ [c] := by
  have := pw_conj [c] [a, b] m
  simpa [D] using this

theorem cell1_Dk (m k : Nat) : Cell 1 (pw D (m + 1)) ([a, b] ++ A k ++ pw D m ++ [c]) 1 := by
  rw [pw_succ]
  have h := (cell1D k).append (cell1_D0 m)
  have e : [a, b] ++ A k ++ [c] ++ pw [a, b, c] m = [a, b] ++ A k ++ pw D m ++ [c] := by
    rw [List.append_assoc ([a, b] ++ A k), c_abc, ← List.append_assoc]
  rwa [e] at h

/-- The single-cell history (C). -/
theorem cell1_C (j m s k : Nat) :
    Cell 1 (pw E j ++ pw D (m + 1) ++ pw E s)
      (A (2 * j + 1) ++ [b] ++ A k ++ pw D m ++ [c] ++ A (2 * s)) 1 := by
  have h := ((cell1_E j).append (cell1_Dk m k)).append (cell1_E s)
  have e : A (2 * j + 1) ++ [b] ++ A k ++ pw D m ++ [c] ++ A (2 * s) =
      A (2 * j) ++ ([a, b] ++ A k ++ pw D m ++ [c]) ++ A (2 * s) := by
    rw [A_add]; simp
  rw [e]; exact h

end LR
end BB25
