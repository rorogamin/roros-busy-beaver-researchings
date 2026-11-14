import RequestProject.ResetRules

/-!
# Blocks

After the counter has overflowed, the machine starts again at the marker with an
empty counter and runs to the right over the material the overflow has released.
That material is always a sequence of **blocks** `44`, `04`, `24`, `14`; `Label`
names their first cells and `cellsOf` expands a sequence of labels back into
tape cells.

Each block has a determined effect on the counter: `44`, `04`, `24` roughly
*double* its gap, whereas a block `14` costs four increments and creates a
radix-3/2 digit, which *multiplies the gap by about 2/3*.  The exact maps are in
`RequestProject.CompletionArithmetic`.
-/

namespace SOC

/-- The first cell of a block; the second one is always a `4`. -/
def Label (x : Sym) : Prop := x = 4 ∨ x = 0 ∨ x = 2 ∨ x = 1

instance : DecidablePred Label := fun x => by unfold Label; infer_instance

/-- The cells of a sequence of blocks. -/
def cellsOf : List Sym → List Sym
  | [] => []
  | x :: L => x :: 4 :: cellsOf L

@[simp] theorem cellsOf_nil : cellsOf [] = [] := rfl

@[simp] theorem cellsOf_cons (x : Sym) (L : List Sym) :
    cellsOf (x :: L) = x :: 4 :: cellsOf L := rfl

theorem cellsOf_append (L₁ L₂ : List Sym) :
    cellsOf (L₁ ++ L₂) = cellsOf L₁ ++ cellsOf L₂ := by
  induction L₁ with
  | nil => rfl
  | cons x L ih => simp [ih]

end SOC
