import RequestProject.Leading

/-!
# The shape of the released block sequence

Writing `L` for the block sequence absorbed by a reset phase, this file computes
the radix pattern of the counter the phase builds (`resetF_pat`, `patF_true`):
the reset phase pushes one radix-2 digit per block, and a block `14`
additionally *converts* the digit pushed by the preceding block into a
radix-3/2 one.

Since an increment never changes a radix (`addT_rad2`) and the overflow releases
a radix-2 digit as a block `44` and a radix-3/2 digit as one of `04`, `24`,
`14`, the sequence released by the next overflow begins with a part `S` of the
same length as `L` carrying a `44` exactly where `L` is not `14`.  This is what
`RequestProject.Completion` uses to compare the two reset computations
(`inherited_exact`); the labels `notOne`, `is4` are the two predicates involved.
-/

namespace SOC

/-! ## Patterns -/

/-- The blocks that are not the expensive block `14`. -/
def notOne (x : Sym) : Bool := x != 1

/-- The blocks `44`. -/
def is4 (y : Sym) : Bool := y == 4

@[simp] theorem notOne_one : notOne 1 = false := rfl
@[simp] theorem is4_four : is4 4 = true := rfl

theorem is4_eq_true {y : Sym} : is4 y = true ↔ y = 4 := by
  simp [is4]

/--
The radix pattern of the counter after a reset phase, as a function of the
pattern it started from: a block pushes a radix-2 digit (`true`), and a block
`14` first turns the lowest digit into a radix-3/2 one (`false`).
The head of the list is the least significant digit.
-/
def patF : List Bool → List Sym → List Bool
  | p, [] => p
  | p, x :: L => patF (if x = 1 then true :: false :: p.tail else true :: p) L

@[simp] theorem patF_nil (p : List Bool) : patF p [] = p := rfl

theorem patF_cons_one (p : List Bool) (L : List Sym) :
    patF p (1 :: L) = patF (true :: false :: p.tail) L := by
  rw [patF]; simp

theorem patF_cons_ne {x : Sym} (hx : x ≠ 1) (p : List Bool) (L : List Sym) :
    patF p (x :: L) = patF (true :: p) L := by
  rw [patF]; simp [hx]

/-- The pattern built from a single radix-2 digit: one entry per block, `false`
exactly at the blocks `14`, and a radix-2 digit at the bottom. -/
theorem patF_true : ∀ (p : List Bool) (L : List Sym),
    patF (true :: p) L = true :: ((L.map notOne).reverse ++ p)
  | p, [] => by simp
  | p, x :: L => by
      by_cases hx : x = 1
      · subst hx
        rw [patF_cons_one, List.tail_cons, patF_true (false :: p) L]
        simp
      · rw [patF_cons_ne hx, patF_true (true :: p) L]
        simp [notOne, hx]

/-! ## The pattern through one revolution -/

/-- **The reset phase builds the pattern `patF`.** -/
theorem resetF_pat : ∀ {w w' : List LD} {L : List Sym}, resetF w L = some w' →
    w'.map rad2 = patF (w.map rad2) L
  | w, w', [], hr => by rw [resetF] at hr; cases hr; simp
  | w, w', x :: L, hr => by
      match x with
      | 4 =>
          rw [resetF] at hr
          rw [resetF_pat hr, patF_cons_ne (by decide)]
          rfl
      | 0 =>
          rw [resetF] at hr
          rw [resetF_pat hr, patF_cons_ne (by decide)]
          rfl
      | 3 => simp at hr
      | 2 =>
          rw [resetF] at hr
          cases hone : addT w 1 with
          | none => rw [hone] at hr; simp at hr
          | some w1 =>
              rw [hone] at hr
              simp only at hr
              rw [resetF_pat hr, patF_cons_ne (by decide)]
              simp [addT_rad2 hone, rad2]
      | 1 =>
          match w with
          | [] => simp at hr
          | .dA :: v => simp at hr
          | .dB :: v => simp at hr
          | .d1 :: v =>
              rw [resetF] at hr
              cases hfour : addT v 4 with
              | none => rw [hfour] at hr; simp at hr
              | some v' =>
                  rw [hfour] at hr
                  simp only at hr
                  rw [resetF_pat hr, patF_cons_one]
                  simp [addT_rad2 hfour, rad2]
          | .d0 :: v =>
              rw [resetF] at hr
              cases hfour : addT v 4 with
              | none => rw [hfour] at hr; simp at hr
              | some v' =>
                  rw [hfour] at hr
                  simp only at hr
                  rw [resetF_pat hr, patF_cons_one]
                  simp [addT_rad2 hfour, rad2]

/-! ## What the shape says about the blocks `14` -/

end SOC
