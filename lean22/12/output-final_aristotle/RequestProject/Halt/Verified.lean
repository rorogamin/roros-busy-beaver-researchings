module

public import RequestProject.Halt.Sound

/-!
# The machine halts

The executable check `HaltEngine.check 44 12 260 524288` computes the exact
eventually periodic level word of cell 44 (prefix of about `7·10^8` letters,
period of about `4.8·10^10` letters, stored eight letters to a byte), and
streams the prefix followed by 12 periods through cells `44, …, 303`.  It
returns `true`: some cell halts on its level word without having emitted a
letter (it is cell 200, on the input `BAAA…`).  By the soundness theorem
`TM5.Eng.halts_of_check` this proves that the machine halts.

The evaluation uses compiled code (`native_decide`), so the Lean compiler and
`Lean.ofReduceBool` are part of the trusted base.  It takes about an hour on
one core and about 25 GB of memory.
-/

@[expose] public section

namespace TM5

/-- Compiled check: the level cascade halts quietly. -/
theorem check_ok : HaltEngine.check 44 12 260 524288 = true := by native_decide

/-- **The machine `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` halts** when started on the
blank tape. -/
theorem halts : Halts := Eng.halts_of_check 44 12 260 524288 (by decide) check_ok

end TM5
