import RequestProject.ResetPhase

/-!
# The machine's first overflow

Started from the blank tape, the machine reaches its first counter overflow
after 306 steps (`run_init_306`, by evaluation); the tape is then

```
.22 B> 44 44 44 44 04 44 04 24 1.
```

i.e. the empty counter in front of the block sequence
`firstBlocks = 44 44 44 04 44 04 24` (the leading `44` belongs to the
configuration `phaseStart`).  This is where the iteration `revIter` of
`RequestProject.Fast` starts.
-/

namespace SOC

set_option maxRecDepth 10000

/-- The block sequence of the first reset phase, after the leading block `44`. -/
def firstBlocks : List Sym := [4, 4, 4, 0, 4, 0, 2]

/-- After 306 steps the machine is at the start of its first reset phase. -/
theorem run_init_306 :
    run init 306 = some (enc ⟨[], 4 :: 4 :: (cellsOf firstBlocks ++ [1])⟩) := by
  rfl

theorem firstBlocks_labels : ∀ x ∈ firstBlocks, Label x := by decide

end SOC
