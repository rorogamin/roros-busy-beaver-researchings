import RequestProject.Chains

/-!
# Reflections off a wall: the triangles of the space-time diagram

In the block description of the tape (see `Chains.lean`) the tape is a concatenation of
blocks `0 4^j 2`; the blocks with `j = 1` form the *bulk*, the blocks with `j ≥ 2` are the
*walls*.  After a rightward sweep the blocks read `1 0^j 3`, and a leftward sweep then
behaves very differently on the two kinds of block:

* a bulk block `1 0 3` is crossed leftwards in `3` steps and becomes `2 0 4`
  (`sweepL_103`);
* a wall block is *not* crossed.  The head performs a short ping-pong on the two cells
  left of the last `0` (`wall_ping`), turns around, and comes back out on the right.  Two
  cells of the wall are consumed, so the wall shrinks by two and the boundary between the
  wall and the bulk on its right moves two cells to the left.

`turn_wall` is that turn-around as a `Bounce` rule, and `bounce_wall_bulk` composes it
with the bulk sweeps on both sides: it describes one complete triangle of the space-time
diagram, for an arbitrary number `k` of bulk blocks between the head and the wall.
-/

namespace BB25

/-! ### The six bulk sweeps, in the general framework

These are the six phases of the period-`6` cycle of a bulk cell, cf. `Blocks.lean`. -/

theorem sweepR_042 : SweepR St.A St.A [0, 4, 2] [1, 0, 3] 3 := by
  have h := sweepR_A0.comp (sweepR_B4.comp sweepR_B2 (by simp)) (by simp)
  norm_num at h
  exact h

theorem sweepR_204 : SweepR St.B St.B [2, 0, 4] [3, 1, 0] 3 := by
  have h := sweepR_B2.comp (sweepR_A0.comp sweepR_B4 (by simp)) (by simp)
  norm_num at h
  exact h

theorem sweepR_420 : SweepR St.B St.B [4, 2, 0] [0, 3, 1] 3 := by
  have h := sweepR_B4.comp (sweepR_B2.comp sweepR_A0 (by simp)) (by simp)
  norm_num at h
  exact h

theorem sweepL_310 : SweepL St.B St.B [3, 1, 0] [4, 2, 0] 3 := by
  have h := (sweepL_B0.comp sweepL_A1 (by simp)).comp sweepL_A3 (by simp)
  norm_num at h
  exact h

theorem sweepL_031 : SweepL St.A St.A [0, 3, 1] [0, 4, 2] 3 := by
  have h := (sweepL_A1.comp sweepL_A3 (by simp)).comp sweepL_B0 (by simp)
  norm_num at h
  exact h

/-! ### The remaining left-pass rules for a block `1 0^j 3`

A leftward sweep in state `A` crosses a block with `j ≤ 2` and is reflected by a block
with `j ≥ 3` (`turn_wall` below). -/

/-- A `j = 0` block `1 3` is crossed leftwards in `2` steps and becomes `4 4`; the head
leaves in state `B`. -/
theorem blockL_13 : SweepL St.A St.B [1, 3] [4, 4] 2 := by
  have h := sweepL_A3.comp sweepL_B1 (by simp)
  norm_num at h
  exact h

lemma blockL_1003_steps (T : ℤ → Sym) (a : ℤ) (h0 : T a = 1) (h1 : T (a + 1) = 0)
    (h2 : T (a + 2) = 0) (h3 : T (a + 3) = 3) :
    step^[6] ⟨St.A, a + 3, T⟩ =
      ⟨St.A, a - 1, wr (wr (wr T a 2) (a + 1) 2) (a + 3) 4⟩ := by
  show step (step (step (step (step (step _))))) = _
  rw [step_A3 T (a + 3) h3, show a + 3 - 1 = a + 2 by ring]
  rw [step_B0 _ (a + 2) (by rw [wr_of_ne _ _ _ (by omega)]; exact h2),
    show a + 2 - 1 = a + 1 by ring]
  rw [step_A0 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega)]; exact h1),
    show a + 1 + 1 = a + 2 by ring]
  rw [step_B0 _ (a + 2)
      (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h2),
    show a + 2 - 1 = a + 1 by ring]
  rw [step_A1 _ (a + 1) (by rw [wr_self]), show a + 1 - 1 = a by ring]
  rw [step_A1 _ a (by
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
    exact h0)]
  congr 1
  funext i
  by_cases e1 : i = a
  · simp [e1, wr, show a ≠ a + 1 by omega]
  by_cases e2 : i = a + 1
  · simp [e2, wr, show a + 1 ≠ a + 3 by omega]
  by_cases e3 : i = a + 3
  · simp [e3, wr]
  · simp [wr, e1, e2, e3]

/-- A `j = 2` block `1 0 0 3` is crossed leftwards in `6` steps and becomes `2 2 0 4`;
the head leaves in state `A`.  (The crossing already involves a small ping-pong.) -/
theorem blockL_1003 : SweepL St.A St.A [1, 0, 0, 3] [2, 2, 0, 4] 6 := by
  intro T a hs
  rw [Seg_cons, Seg_cons, Seg_cons, Seg_cons] at hs
  obtain ⟨h0, h1, h2, h3, -⟩ := hs
  rw [show a + 1 + 1 = a + 2 by ring] at h2
  rw [show a + 1 + 1 + 1 = a + 3 by ring] at h3
  refine ⟨wr (wr (wr T a 2) (a + 1) 2) (a + 3) 4, ?_, ?_, ?_⟩
  · have hp : a + ((([1, 0, 0, 3] : List Sym).length : ℕ) : ℤ) - 1 = a + 3 := by simp; ring
    rw [hp, blockL_1003_steps T a h0 h1 h2 h3]
  · rw [Seg_cons, Seg_cons, Seg_cons, Seg_cons]
    refine ⟨?_, ?_, ?_, ?_, Seg_nil _ _⟩
    · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
    · rw [wr_of_ne _ _ _ (by omega), wr_self]
    · rw [show a + 1 + 1 = a + 2 by ring, wr_of_ne _ _ _ (by omega),
        wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]
      exact h2
    · rw [show a + 1 + 1 + 1 = a + 3 by ring, wr_self]
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]

/-! ### The wall turn-around -/

/-- The ping-pong at the right end of a wall: entering the run of `0`s from the right in
state `B`, the head spends `6` steps turning the two cells to its left into `1 3` and
comes back to where it started, now in state `A`. -/
lemma wall_ping (T : ℤ → Sym) (a : ℤ) (h0 : T a = 0) (h1 : T (a + 1) = 0)
    (h2 : T (a + 2) = 0) :
    step^[6] ⟨St.B, a + 2, T⟩ = ⟨St.A, a + 2, wr (wr T a 1) (a + 1) 3⟩ := by
  show step (step (step (step (step (step _))))) = _
  rw [step_B0 T (a + 2) h2, show a + 2 - 1 = a + 1 by ring]
  rw [step_A0 T (a + 1) h1, show a + 1 + 1 = a + 2 by ring]
  rw [step_B0 _ (a + 2) (by rw [wr_of_ne _ _ _ (by omega)]; exact h2),
    show a + 2 - 1 = a + 1 by ring]
  rw [step_A1 _ (a + 1) (by rw [wr_self]), show a + 1 - 1 = a by ring]
  rw [step_A0 _ a (by rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact h0)]
  rw [step_B2 _ (a + 1) (by rw [wr_of_ne _ _ _ (by omega), wr_self])]
  congr 1
  · ring
  · funext i
    by_cases e1 : i = a
    · simp [e1, wr, show a ≠ a + 1 by omega]
    by_cases e2 : i = a + 1
    · simp [e2, wr]
    · simp [wr, e1, e2]

/-- The complete turn-around at the right end of a wall, as a step computation:
`0 0 0 3` with the head on the `3` in state `A` becomes `1 3 1 0`, the head leaving on the
right in state `B` after exactly `9` steps. -/
lemma wall_turn_steps (T : ℤ → Sym) (a : ℤ) (h0 : T a = 0) (h1 : T (a + 1) = 0)
    (h2 : T (a + 2) = 0) (h3 : T (a + 3) = 3) :
    step^[9] ⟨St.A, a + 3, T⟩ =
      ⟨St.B, a + 4, wr (wr (wr (wr T a 1) (a + 1) 3) (a + 2) 1) (a + 3) 0⟩ := by
  have e : (9 : ℕ) = 2 + (6 + 1) := by norm_num
  rw [e, Function.iterate_add_apply, Function.iterate_add_apply]
  -- first step: `A` reads the `3`
  show step^[2] (step^[6] (step ⟨St.A, a + 3, T⟩)) = _
  rw [step_A3 T (a + 3) h3, show a + 3 - 1 = a + 2 by ring]
  -- the ping-pong, on a tape that has a `4` at `a + 3`
  set T1 := wr T (a + 3) 4 with hT1
  have v0 : T1 a = 0 := by rw [hT1, wr_of_ne _ _ _ (by omega)]; exact h0
  have v1 : T1 (a + 1) = 0 := by rw [hT1, wr_of_ne _ _ _ (by omega)]; exact h1
  have v2 : T1 (a + 2) = 0 := by rw [hT1, wr_of_ne _ _ _ (by omega)]; exact h2
  rw [wall_ping T1 a v0 v1 v2]
  -- the last two steps: out over the `0` and the `4`
  set T2 := wr (wr T1 a 1) (a + 1) 3 with hT2
  show step (step ⟨St.A, a + 2, T2⟩) = _
  rw [step_A0 T2 (a + 2) (by
    rw [hT2, wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega)]; exact v2)]
  rw [show a + 2 + 1 = a + 3 by ring]
  rw [step_B4 _ (a + 3) (by
    rw [wr_of_ne _ _ _ (by omega), hT2, wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega), hT1, wr_self])]
  congr 1
  · ring
  · funext i
    by_cases e1 : i = a
    · simp [e1, hT2, hT1, wr, show a ≠ a + 1 by omega, show a ≠ a + 2 by omega,
        show a ≠ a + 3 by omega]
    by_cases e2 : i = a + 1
    · simp [e2, hT2, hT1, wr, show a + 1 ≠ a + 2 by omega, show a + 1 ≠ a + 3 by omega]
    by_cases e3 : i = a + 2
    · simp [e3, wr, show a + 2 ≠ a + 3 by omega]
    by_cases e4 : i = a + 3
    · simp [e4, wr]
    · simp [hT2, hT1, wr, e1, e2, e3, e4]

/-- **Wall turn-around.**  The head, sweeping leftwards in state `A`, meets the right end
`0 0 0 3` of a wall; `9` steps later it is on its way back to the right in state `B`, and
the wall end reads `1 3 1 0`: two cells of the wall have been eaten. -/
theorem turn_wall : Bounce St.A St.B [0, 0, 0, 3] [1, 3, 1, 0] 9 := by
  intro T a hs
  rw [Seg_cons, Seg_cons, Seg_cons, Seg_cons] at hs
  obtain ⟨h0, h1, h2, h3, -⟩ := hs
  have e1 : a + 1 + 1 = a + 2 := by ring
  have e2 : a + 1 + 1 + 1 = a + 3 := by ring
  rw [e1] at h2
  rw [e2] at h3
  refine ⟨wr (wr (wr (wr T a 1) (a + 1) 3) (a + 2) 1) (a + 3) 0, ?_, ?_, ?_⟩
  · have hp : a + ((([0, 0, 0, 3] : List Sym).length : ℕ) : ℤ) - 1 = a + 3 := by
      simp; ring
    rw [hp, wall_turn_steps T a h0 h1 h2 h3]
    congr 1
  · rw [Seg_cons, Seg_cons, Seg_cons, Seg_cons]
    refine ⟨?_, ?_, ?_, ?_, Seg_nil _ _⟩
    · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
        wr_self]
    · rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_self]
    · rw [e1, wr_of_ne _ _ _ (by omega), wr_self]
    · rw [e1, show a + 2 + 1 = a + 3 by ring, wr_self]
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rw [wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega), wr_of_ne _ _ _ (by omega),
      wr_of_ne _ _ _ (by omega)]

/-! ### A complete triangle -/

/-- **One triangle of the space-time diagram.**  The head enters a region consisting of
the right end of a wall followed by `k` bulk blocks, sweeping leftwards in state `A`; it
crosses the `k` blocks (turning `1 0 3` into `2 0 4`), eats two cells of the wall, and
comes back out on the right in state `B` after exactly `6k + 9` steps, having turned the
bulk into `3 1 0` blocks.  The rule holds for every `k`, and in particular the machine
does not halt anywhere inside such a triangle. -/
theorem bounce_wall_bulk (k : ℕ) :
    Bounce St.A St.B ([0, 0, 0, 3] ++ rep [1, 0, 3] k) ([1, 3, 1, 0] ++ rep [3, 1, 0] k)
      (k * 3 + 9 + k * 3) :=
  Bounce.comp (sweepL_bulk k) turn_wall (sweepR_rep sweepR_204 (by simp) k)
    (by simp) (by simp)

end BB25
