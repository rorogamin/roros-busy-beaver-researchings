import Accel.Sim

/-!
# Certified lower bound on the running time

The certified accelerated simulator of `Accel/Sim.lean`, evaluated by compiled
code (`native_decide`), runs the machine from the blank tape past `10^1000`
steps.  By `no_halt_of_runAccel` this proves that the machine does not halt
within its first `10^1000` steps.
-/

namespace TM2x5

theorem runAccel_reaches_ten_pow_thousand :
    (runAccel 100000000000 (10 ^ 1000) init 0).isSome = true := by
  native_decide

/-- The machine `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA` does not halt within its first
`10^1000` steps when started on the blank tape. -/
theorem not_halted_within_ten_pow_thousand : ∀ n ≤ 10 ^ 1000, run n ≠ none :=
  no_halt_of_runAccel runAccel_reaches_ten_pow_thousand

end TM2x5
