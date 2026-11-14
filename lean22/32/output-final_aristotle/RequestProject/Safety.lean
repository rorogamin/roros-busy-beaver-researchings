import RequestProject.Counter
import RequestProject.MacroMachine

/-!
# Where the machine can die

The macro machine of `RequestProject.MacroMachine` is **total** except at two
patterns, and at those two patterns the Turing machine really does halt.  So the
macro model captures halting exactly:

* `B> x3` with `x = 0` or `x = 4` — the head runs into the right-hand cell of a
  digit `23`/`03` from the left;
* `B> 1` with a digit `23`/`03` (or nothing at all) next to the head — the head
  reads the terminating `1` of the right-hand material while the lowest digit of
  the counter is one of the radix-3/2 digits.

Everything else is safe, whatever the counter and the tape context are.  What
this file still provides is `BinHead`, the property "the lowest digit of the
counter is a radix-2 digit", which is exactly what keeps the second pattern out
of reach, and the case analysis `sym_cases`.
-/

namespace SOC

open Cfg

/-- The lowest digit of the counter is one of the radix-2 digits `02`, `22`. -/
def BinHead : List LD → Prop
  | .d0 :: _ => True
  | .d1 :: _ => True
  | _ => False

instance : DecidablePred BinHead := fun w => by
  match w with
  | [] => exact inferInstanceAs (Decidable False)
  | .d0 :: _ => exact inferInstanceAs (Decidable True)
  | .d1 :: _ => exact inferInstanceAs (Decidable True)
  | .dA :: _ => exact inferInstanceAs (Decidable False)
  | .dB :: _ => exact inferInstanceAs (Decidable False)

theorem sym_cases (x : Sym) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  revert x; decide

/-! ## The dangerous patterns really are fatal -/

/-! ## A criterion for non-halting -/

end SOC
