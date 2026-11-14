module

public import RequestProject.Halt.Sound

/-!
# The machine halts

The executable check `HaltEngine.check 170 1 80 524288` computes the exact
eventually periodic level word of cell 170 (period of `3 831 101 441`
letters, stored eight letters to a byte), and streams its prefix followed by
one period through cells `170, …, 249`.  It returns `true`: some cell halts on
its level word without having emitted a letter (by the independent C
computations this is cell 238, on an input beginning with `B A B A`).  By the
soundness theorem `BCM.Eng.halts_of_check` this proves that the machine halts.

The evaluation uses compiled code (`native_decide`), so the Lean compiler and
`Lean.ofReduceBool` are part of the trusted base.
-/

@[expose] public section

namespace BCM

/-- Compiled check: the level cascade halts quietly. -/
theorem check_ok : HaltEngine.check 170 1 80 524288 = true := by native_decide

/-- **The machine `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---` halts** when started on the
blank tape. -/
theorem halts : Halts := Eng.halts_of_check 170 1 80 524288 (by decide) check_ok

end BCM
