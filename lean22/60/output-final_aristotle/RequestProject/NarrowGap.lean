import RequestProject.Local
import RequestProject.NonHalting

/-!
# A local configuration in which the machine *does* halt

Every macro rule of this development needs **three** blank cells to the left of the head:
its window begins `0 0 0`.  That hypothesis is not an artefact of how the rules were
stated — with fewer blank cells the machine can run into its one halting transition.  This
file records the smallest such configuration:

```
      0 0 1 0 0          the head in state B on the last cell
                         →  13 steps later the machine has halted
```

The `1` is the cell a rightward sweep leaves at the left end of a swept `4`-run
(`four_run_to_zero_run` rewrites `U(a,1) = 0 4^a 2` as `1 0^a 3`), and the head sits on the
leftmost cell of the tape word to its right, which in the token alphabet is always a `0`.
So this is exactly a left-end step attempted with one spare blank cell instead of three.

Two consequences worth stating.  First, the `0 0 0` in every window rule is load-bearing:
no rule of the catalogue can be weakened to two blank cells.  Second, the machine is *not*
non-halting for soft reasons — it is one miscounted cell away from halting, so any proof
must control the arithmetic of the run lengths, which is precisely the `3j+1` of the
fractal identity (`ANALYSIS.md` §20).  Simulation bears this out: probing an isolated
`4`-run `U(a,1)` after the `P3` prefix, with a padding of tokens `u` (`sim/self2.py`), the
machine halts for `a = 6` and `a = 15`, while every length `a = 3j+1` that actually occurs
in the orbit runs on.  That last observation is simulation only; the theorem below is
machine-checked.
-/

namespace BB25

/-- **The machine halts in a narrow gap.**  If the tape reads `0 0 1 0 0` and the head is
in state `B` on the last of those five cells, then `13` steps later the machine has
halted.  Nothing outside the five cells is read, so the rest of the tape is arbitrary.

The `1` is the cell a rightward sweep leaves at the left end of a swept `4`-run, and the
head is on the leftmost cell of the tape word to its right — which, in the token alphabet,
always is a `0`.  So this is a left-end step attempted with one spare blank cell instead of
three. -/
theorem halt_of_narrow_gap (T : ℤ → Sym) (a : ℤ) (h : Seg T a [0, 0, 1, 0, 0]) :
    Halted (step^[13] ⟨St.B, a + ((4 : ℕ) : ℤ), T⟩) := by
  have hw : Win St.B St.A 4 2 [0, 0, 1, 0, 0] [1, 3, 4, 3, 0] 12 :=
    Win.of_lrun (by decide)
  obtain ⟨T', hstep, hseg, -⟩ := hw T a h
  have h4 : T' (a + ((2 : ℕ) : ℤ)) = 4 := by simpa using hseg 2 (by simp)
  have hsucc : step^[13] ⟨St.B, a + ((4 : ℕ) : ℤ), T⟩
      = step (step^[12] ⟨St.B, a + ((4 : ℕ) : ℤ), T⟩) :=
    Function.iterate_succ_apply' step 12 _
  rw [hsucc, hstep, step_A4 T' _ h4]
  rfl

/-- The same statement cell by cell: if the head is in state `B` on a cell `a+4` whose
four left neighbours read `0 0 1 0`, the machine halts thirteen steps later.  Non-halting
therefore forces the swept `4`-runs to avoid leaving exactly one spare blank cell. -/
theorem halt_of_one_spare_blank (T : ℤ → Sym) (a : ℤ)
    (h0 : T a = 0) (h1 : T (a + 1) = 0) (h2 : T (a + 2) = 1) (h3 : T (a + 3) = 0)
    (h4 : T (a + 4) = 0) :
    Halted (step^[13] ⟨St.B, a + 4, T⟩) := by
  have hseg : Seg T a [0, 0, 1, 0, 0] := by
    refine Seg_cons.mpr ⟨h0, Seg_cons.mpr ⟨?_, Seg_cons.mpr ⟨?_, Seg_cons.mpr ⟨?_, ?_⟩⟩⟩⟩
    · simpa using h1
    · rw [show a + 1 + 1 = a + 2 by ring]; exact h2
    · rw [show a + 1 + 1 + 1 = a + 3 by ring]; exact h3
    · refine Seg_cons.mpr ⟨?_, by simp⟩
      rw [show a + 1 + 1 + 1 + 1 = a + 4 by ring]; exact h4
  have := halt_of_narrow_gap T a hseg
  simpa using this

end BB25
