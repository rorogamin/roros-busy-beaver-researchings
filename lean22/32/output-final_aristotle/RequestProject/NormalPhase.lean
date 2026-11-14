import RequestProject.FirstPhase
import RequestProject.OneSafe

/-!
# The normal phase

With blank tape to its right the machine repeats the cycle

```
w B> .  ⟶  w B> 21  ⟶  inc(w) B> 41  ⟶  inc(w) 03 B> .
```

(`normal_cycle`): it writes two cells of new right-hand material and pushes a
radix-3/2 digit `03` onto the counter, at the cost of one increment.  This is
"the left counter counts down by one and the right counter counts up by one" of
the informal analysis, and it strictly decreases the gap,
`(2g-1)/3 < g` (`gap_normal_cycle_lt`), so the counter overflows after finitely
many cycles.  `normal_overflow` follows the overflow itself, which releases the
counter's digits as blocks `44|04|24|14` closed by a terminating `1` — the
configuration `phaseStart L'` at which the next reset phase begins.  The normal
phase needs no arithmetic hypothesis at all.
-/

namespace SOC

open Cfg

/-! ## The junction: reading the last `1` of the old right-hand material -/

/-! ## The normal phase -/

/-- **One cycle of the normal phase.**  Facing blank tape, the machine writes
two cells, performs one increment and pushes a radix-3/2 digit `03`. -/
theorem normal_cycle {w w' : List LD} (h : Inc w w') :
    MSteps ⟨w, []⟩ ⟨.dB :: w', []⟩ := by
  have s1 : MStep ⟨w, ([] : List Sym)⟩ ⟨w, [2, 1]⟩ := MStep.a00 (r := ([] : List Sym)) rfl rfl
  have s2 : MStep ⟨w, [2, 1]⟩ ⟨w', [4, 1]⟩ := MStep.inc2 (r := [2, 1]) h rfl
  have s3 : MStep ⟨w', [4, 1]⟩ ⟨.dB :: w', []⟩ := MStep.a41 (r := [4, 1]) rfl rfl
  exact ((MSteps.single s1).tail s2).tail s3

/-- **The end of the normal phase.**  When the counter can no longer be
incremented the cycle overflows instead: the marker moves one cell left, the old
counter is released to the right as the new right-hand material, and the
terminating `1` written by the last cycle closes it off. -/
theorem normal_overflow {w : List LD} {s : List Sym} (h : Ovf w s) :
    MSteps ⟨w, []⟩ ⟨[], 4 :: 4 :: (s ++ [1])⟩ := by
  have s1 : MStep ⟨w, ([] : List Sym)⟩ ⟨w, [2, 1]⟩ := MStep.a00 (r := ([] : List Sym)) rfl rfl
  have s2 : MStep ⟨w, [2, 1]⟩ ⟨[], 4 :: 4 :: (s ++ [1])⟩ := MStep.ovf2 (r := [2, 1]) h rfl
  exact (MSteps.single s1).tail s2

/-- Pushing a digit `03` after an increment strictly decreases the gap. -/
theorem gap_normal_cycle_lt {w w' : List LD} (h : Inc w w') (hp : 0 < gap w) :
    gap (.dB :: w') < gap w := by
  have := h.gap_eq
  simp only [gap_dB]
  omega

/-! ## One whole revolution -/

/-- The configuration at the start of a reset phase: an empty counter, a block
`44`, the released blocks `L`, and the terminating `1`. -/
def phaseStart (L : List Sym) : MCfg := ⟨[], 4 :: 4 :: (cellsOf L ++ [1])⟩

end SOC
