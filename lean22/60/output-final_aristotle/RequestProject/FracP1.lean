import RequestProject.CarryU21V

/-!
# The `P1` row of the census with a `U(2,2) V(1)` inside the tape

This file proves the remaining `P1` row of the census of `ANALYSIS.md` §36: the macro step
in which the token that stops the carry is the *prefix of a `P3` configuration sitting
inside the tape*,

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · U(1,2m+2) 0
       --(237 + 12r + 40m) steps-->
   U(2,2) u · U(2,1) · u^(r+2) · U(2,2m+10) 0
```

Unlike every rule proved so far, the head makes **four** passes over the region rather than
two: the inner `U(2,2) V(1) u` is itself the left end of a `P3` configuration, so the carry
is turned around twice before it comes back.  This is the fractal of `ANALYSIS.md` §20 in
miniature, and it is why the step count is so much larger than for the two-pass rules.

The proof exhibits the computation as twenty-eight macro steps, grouped into three
lemmas: `p1fr_pass12` (the first two passes, `97 + 3r + 20m` steps), `p1fr_pass34`
(the two further passes, `118 + 6r + 20m` steps) and `p1fr_close` (the return to the left
end, `22 + 3r` steps).
-/

namespace BB25

/-! ### The new fixed pieces -/

/-- The twelve steps in which the carry, having crossed `U(2,1)`'s `4`-run, turns around
inside `U(2,2) V(1)` and starts rightwards again. -/
theorem fp1_turn12 :
    Win St.A St.A 2 6 [0, 3, 2, 4, 3, 2, 0] [1, 1, 0, 1, 0, 3, 0] 12 :=
  Win.of_lrun (by decide)

/-- Two steps: the head, back at the marker left by the return sweep, turns around. -/
theorem fp1_turn2 : Win St.A St.A 0 2 [0, 2, 0] [1, 3, 0] 2 :=
  Win.of_lrun (by decide)

/-- The four steps in which the return sweep leaves the run of `1`s and crosses the
marker `1 0 3`.  The cell at the far end is reached but never read, so it may carry any
symbol. -/
theorem fp1_ret4_gen (x : Sym) :
    Win St.A St.B 4 0 (x :: [3, 1, 0, 3]) (x :: [4, 2, 0, 4]) 4 := by
  fin_cases x <;> exact Win.of_lrun (by decide)

/-- `fp1_ret4_gen` in the case that occurs in `rule_P1_fractal`. -/
theorem fp1_ret4 : Win St.A St.B 4 0 [1, 3, 1, 0, 3] [1, 4, 2, 0, 4] 4 :=
  fp1_ret4_gen 1

/-- The five steps in which the head, in state `B` at the right end of the three `1`s the
turn-around left, walks over them and reaches the last marker. -/
theorem fp1_ones3 : Win St.B St.A 5 0 [3, 1, 0, 1, 1, 1] [3, 2, 0, 4, 4, 4] 5 :=
  Win.of_lrun (by decide)

/-- Two steps: the head crosses the `3` at the left end of a swept block and stops on the
`0` beyond it. -/
theorem fp1_two : Win St.A St.A 2 0 [0, 0, 3] [0, 0, 4] 2 :=
  Win.of_lrun (by decide)

/-- The reflection inside a run of `0`s: the head, arriving leftwards, is turned around
after four steps and starts rightwards again in state `B`. -/
theorem fp1_reflect : Win St.A St.B 1 1 [0, 0, 0] [1, 2, 0] 4 :=
  Win.of_lrun (by decide)

/-- The seven steps in which the second rightward pass crosses the (already swept) token
`U(4,1)`. -/
theorem fp1_crossU41 :
    Win St.B St.A 0 7 [2, 0, 4, 4, 4, 4, 2, 0] [3, 1, 0, 0, 0, 0, 3, 0] 7 :=
  Win.of_lrun (by decide)

/-- One step: in state `B` on a `1`, write `4` and move left. -/
theorem fp1_B1 : Win St.B St.B 1 0 [0, 1] [0, 4] 1 :=
  Win.of_lrun (by decide)

/-- Four steps of the final leftward pass, over the last swept block. -/
theorem fp1_pre : Win St.B St.A 4 0 [0, 0, 3, 1, 0] [0, 0, 4, 2, 0] 4 :=
  Win.of_lrun (by decide)

/-- The closing six steps: the head rebuilds the prefix `U(2,2)` and stops on the new
leftmost non-blank cell. -/
theorem fp1_close : Win St.A St.B 4 0 [0, 1, 3, 1, 0, 0] [0, 4, 4, 2, 2, 0] 6 :=
  Win.of_lrun (by decide)

/-- The eight steps in which the final leftward pass leaves the run of `2`s and crosses
the two blocks next to it. -/
theorem fp1_backL :
    Win St.A St.B 8 0 [0, 3, 1, 0, 3, 1, 0, 1, 3] [0, 4, 2, 0, 4, 2, 0, 4, 4] 8 :=
  Win.of_lrun (by decide)

/-! ### The first two passes -/

/-- **The first two passes.**  Starting from the `P1` configuration
`U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · U(1,2m+2)`, the carry crosses the run of `u`s,
is turned around inside `U(2,2) V(1)`, delivers four `2`s into `U(1,2m+2)`, comes back to
the marker the turn-around left, and goes out and back a second time.  After exactly
`97 + 3r + 20m` steps the head is in state `B` on the cell `3r+20`. -/
theorem p1fr_pass12 (r m : ℕ) :
    Win St.B St.B 3 (3 * r + 20)
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++ tokV 1 ++
        tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1, 1, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
      (97 + 3 * r + 20 * m) := by
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  have q4 : List.replicate (2 * m + 4) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 4 = 2 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  -- stage A : the opening
  have HA := p1g_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++
      (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage B : the carry crosses the run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3]
    ([4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))
  -- stage C : the `4`-run of `U(2,2)`
  have HC := (Win.of_sweepR hblk (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1))
    ([4, 3, 2, 0, 4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))
  -- stage D : the turn-around inside `U(2,2) V(1)`
  have HD := fp1_turn12.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0])
    ([4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))
  -- stage E : the `u` after the `V`
  have HE := (Win.of_sweepR sweepR_042 (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3])
    ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))
  -- stage F : the absorbing token
  have HF := (Win.of_sweepR sweepR_042 (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3])
    (List.replicate (2 * m) 2 ++ [0])
  -- stage G : the round trip through the run of `2`s
  have HG := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3, 1, 0]) []
  -- stage H : the `u` crossed leftwards
  have HH := (Win.of_sweepL (sweepL_bulk 1) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage I : the `V` crossed leftwards
  have HI := (Win.of_sweepL (sweepL_bulk 1) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    ([2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage J : the second turn-around
  have HJ := fp1_turn2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    ([4, 2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage K : the second rightward pass
  have HK := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) 2) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3])
    (List.replicate (2 * m + 2) 2 ++ [0])
  -- stage L : the ping-pong through the run of `2`s
  have HL := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3, 1, 0, 3, 1]) [0]
  -- stage M : the turn-around at the far end
  have HM := rule_endgame.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3, 1, 0, 3, 1] ++ List.replicate (2 * m + 2) 1) []
  -- stage N : the return sweep over the run of `1`s
  have HN := (onesBack_gen 3 (2 * m + 6)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3, 1, 0]) []
  -- stage O : the marker is crossed
  have HO := fp1_ret4.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    (List.replicate (2 * m + 6) 2 ++ [0])
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++
        tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])) := by
    rw [rep_succ]; simp
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([0, 4, 4, 2] ++ [2]) ++
        ([4, 3, 2, 0, 4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) := by
    simp
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([1, 0, 0, 3] ++ [2]) ++
        ([4, 3, 2, 0, 4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        [0, 3, 2, 4, 3, 2, 0] ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) := by
    simp
  have E4 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        [1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3]) ++ ([0, 4, 2] ++ [0]) ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) := by
    simp
  have E5 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3]) ++ ([1, 0, 3] ++ [0]) ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3]) ++ ([0, 4, 2] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q2]; simp
  have E6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3]) ++ ([1, 0, 3] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3, 1, 0]) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [q1]; simp
  have E7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3, 1, 0]) ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0]) ++ ((3 : Sym) :: rep [1, 0, 3] 1) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp [rep_succ]
  have E8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0]) ++ ((3 : Sym) :: rep [2, 0, 4] 1) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ((0 : Sym) :: rep [1, 0, 3] 1) ++
        ([2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    simp [rep_succ]
  have E9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ((0 : Sym) :: rep [2, 0, 4] 1) ++
        ([2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [0, 2, 0] ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    simp [rep_succ]
  have E10 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [1, 3, 0] ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3]) ++ (rep [0, 4, 2] 2 ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [q4]; simp [rep_succ]
  have E11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3]) ++ (rep [1, 0, 3] 2 ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0, 3, 1]) ++
        ([0, 3] ++ List.replicate (2 * (m + 1) + 1) 2) ++ [0] := by
    rw [show 2 * (m + 1) + 1 = 1 + (2 * m + 2) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 2)]
    simp [rep_succ]
  have E12 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0, 3, 1]) ++
        (List.replicate (2 * (m + 1)) 1 ++ [0, 3, 2]) ++ [0] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0, 3, 1] ++ List.replicate (2 * m + 2) 1) ++
        [0, 3, 2, 0] ++ [] := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring]; simp
  have E13 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0, 3, 1] ++ List.replicate (2 * m + 2) 1) ++
        [1, 1, 1, 0] ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 1 ++ [0])) ++ [] := by
    have e : List.replicate (2 * m + 6) (1 : Sym)
        = 1 :: (List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) := by
      rw [show 2 * m + 6 = 1 + ((2 * m + 2) + 3) from by ring, replicate_split,
        replicate_split]
      rfl
    rw [e]; simp
  have E14 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3, 1, 0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [1, 3, 1, 0, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp
  have E15 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [1, 4, 2, 0, 4] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1, 1, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp
  -- chain the stages
  have SA : Win St.B St.A 3 13 _ _ 16 := HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 13 (3 * r + 16) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC : Win St.A St.A (3 * r + 16) (3 * r + 20) _ _ 4 :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 rfl
  have SD : Win St.A St.A (3 * r + 20) (3 * r + 24) _ _ 12 :=
    HD.cast (by simp; ring) (by simp; ring) rfl E4 rfl
  have SE : Win St.A St.A (3 * r + 24) (3 * r + 27) _ _ 3 :=
    HE.cast (by simp; ring) (by simp; ring) rfl E5 rfl
  have SF : Win St.A St.A (3 * r + 27) (3 * r + 30) _ _ 3 :=
    HF.cast (by simp; ring) (by simp; ring) rfl E6 rfl
  have SG : Win St.A St.A (3 * r + 30) (3 * r + 26) _ _ (10 * m + 14) :=
    HG.cast (by simp; ring) (by simp; ring) rfl E7 rfl
  have SH : Win St.A St.A (3 * r + 26) (3 * r + 23) _ _ 3 :=
    HH.cast (by simp; ring) (by simp; ring) rfl E8 rfl
  have SI : Win St.A St.A (3 * r + 23) (3 * r + 20) _ _ 3 :=
    HI.cast (by simp; ring) (by simp; ring) rfl E9 rfl
  have SJ : Win St.A St.A (3 * r + 20) (3 * r + 22) _ _ 2 :=
    HJ.cast (by simp; ring) (by simp; ring) rfl E10 rfl
  have SK : Win St.A St.A (3 * r + 22) (3 * r + 28) _ _ 6 :=
    HK.cast (by simp; ring) (by simp; ring) rfl E11 (by ring)
  have SL : Win St.A St.A (3 * r + 28) (3 * r + 2 * m + 30) _ _ (8 * m + 8) :=
    HL.cast (by simp; ring) (by simp; ring) rfl E12 (by ring)
  have SM : Win St.A St.B (3 * r + 2 * m + 30) (3 * r + 2 * m + 31) _ _ 9 :=
    HM.cast (by simp; ring) (by simp; ring) rfl E13 rfl
  have SN : Win St.B St.A (3 * r + 2 * m + 31) (3 * r + 24) _ _ (2 * m + 7) :=
    HN.cast (by simp; ring) (by simp; ring) rfl E14 (by ring)
  have SO : Win St.A St.B (3 * r + 24) (3 * r + 20) _ _ 4 :=
    HO.cast (by simp; ring) (by simp; ring) rfl E15 rfl
  have T1 := SA.trans SB (by simp; omega)
  have T2 := T1.trans SC (by simp; omega)
  have T3 := T2.trans SD (by simp; omega)
  have T4 := T3.trans SE (by simp; omega)
  have T5 := T4.trans SF (by simp; omega)
  have T6 := T5.trans SG (by simp; omega)
  have T7 := T6.trans SH (by simp; omega)
  have T8 := T7.trans SI (by simp; omega)
  have T9 := T8.trans SJ (by simp; omega)
  have T10 := T9.trans SK (by simp; omega)
  have T11 := T10.trans SL (by simp; omega)
  have T12 := T11.trans SM (by simp; omega)
  have T13 := T12.trans SN (by simp; omega)
  exact (T13.trans SO (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The last two passes -/

/-- **The last two passes.**  From the configuration the first two passes leave, the head
walks back to the run of `0`s left by the swept `U(4,1)`, is reflected there, crosses the
whole region a third time, is reflected once more and delivers the last two `2`s.  This
takes exactly `118 + 6r + 20m` steps. -/
theorem p1fr_pass34 (r m : ℕ) :
    Win St.B St.A (3 * r + 20) (3 * r + 20)
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1, 1, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 10) 2 ++ [0]))
      (118 + 6 * r + 20 * m) := by
  have p6 : List.replicate (2 * m + 6) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * m + 4) 2 := by
    rw [show 2 * m + 6 = 2 + (2 * m + 4) from by ring,
      replicate_split (2 : Sym) 2 (2 * m + 4)]; rfl
  have p5 : List.replicate (2 * m + 5) (2 : Sym)
      = 2 :: List.replicate (2 * m + 4) 2 := by
    rw [show 2 * m + 5 = 1 + (2 * m + 4) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 4)]; rfl
  have p8 : List.replicate (2 * m + 8) (2 : Sym)
      = 2 :: List.replicate (2 * m + 7) 2 := by
    rw [show 2 * m + 8 = 1 + (2 * m + 7) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 7)]; rfl
  have p7 : List.replicate (2 * m + 7) (2 : Sym)
      = 2 :: List.replicate (2 * m + 6) 2 := by
    rw [show 2 * m + 7 = 1 + (2 * m + 6) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 6)]; rfl
  -- the two round trips through the run of `2`s, with their exponents normalised
  have cb2 : Win St.A St.A 4 0
      ([3, 1, 0, 3] ++ (List.replicate (2 * m + 5) 2 ++ [0]))
      (3 :: (List.replicate (2 * m + 8) 2 ++ [0])) (10 * m + 34) :=
    (cross_back (m + 2)).cast rfl rfl
      (by rw [show 2 * (m + 2) + 1 = 2 * m + 5 from by ring])
      (by rw [show 2 * (m + 2) + 4 = 2 * m + 8 from by ring]) (by ring)
  have cb3 : Win St.A St.A 4 0
      ([3, 1, 0, 3] ++ (List.replicate (2 * m + 7) 2 ++ [0]))
      (3 :: (List.replicate (2 * m + 10) 2 ++ [0])) (10 * m + 44) :=
    (cross_back (m + 3)).cast rfl rfl
      (by rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by ring])
      (by rw [show 2 * (m + 3) + 4 = 2 * m + 10 from by ring]) (by ring)
  -- stage P : the three `1`s the turn-around left
  have HP := fp1_ones3.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage Q : the run of `u`s crossed leftwards
  have HQ := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0]
    ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage R : into the run of `0`s
  have HR := fp1_two.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0]
    (rep [2, 0, 4] (r + 1) ++
      ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
  -- stage S : the reflection
  have HS := fp1_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    ([4] ++ (rep [2, 0, 4] (r + 1) ++
      ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))
  -- stage T : the third rightward pass over the run of `u`s
  have HT := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 2)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1]
    ([0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage U : the swept `U(4,1)`
  have HU := fp1_crossU41.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2))
    ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage V : the token before the run of `2`s
  have HV := (Win.of_sweepR sweepR_042 (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0, 3])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage W : the third round trip through the run of `2`s
  have HW := cb2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0]) []
  -- stage X : back into the run of `0`s
  have HX := fp1_two.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0])
    (List.replicate (2 * m + 8) 2 ++ [0])
  -- stage Y : the second reflection
  have HY := fp1_reflect.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0])
    ([4] ++ (List.replicate (2 * m + 8) 2 ++ [0]))
  -- stage Z : one block crossed rightwards
  have HZ := (Win.of_sweepR sweepR_204 (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1])
    (List.replicate (2 * m + 7) 2 ++ [0])
  -- stage AA : one step into the run of `2`s
  have HAA := carry_B2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3, 1, 0])
    (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage BB : the fourth round trip through the run of `2`s
  have HBB := cb3.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) []
  -- the tape words the computation passes through
  have F0 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1, 1, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 1, 0, 1, 1, 1] ++ ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have F1 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 2, 0, 4, 4, 4] ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [1, 0, 3] (r + 1)) ++
        ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have F2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [2, 0, 4] (r + 1)) ++
        ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0] ++ [0, 0, 3] ++
        (rep [2, 0, 4] (r + 1) ++
          ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) := by
    simp
  have F3 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0] ++ [0, 0, 4] ++
        (rep [2, 0, 4] (r + 1) ++
          ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++
            (List.replicate (2 * m + 6) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0] ++
        ([4] ++ (rep [2, 0, 4] (r + 1) ++
          ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) := by
    simp
  have F4 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] (r + 1) ++
          ([2, 0, 4, 4, 4, 4, 2, 0, 4] ++
            (List.replicate (2 * m + 6) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ (rep [2, 0, 4] (r + 2) ++ [2]) ++
        ([0, 4, 4, 4, 4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp [rep_succ]
  have F5 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ (rep [3, 1, 0] (r + 2) ++ [2]) ++
        ([0, 4, 4, 4, 4, 2, 0, 4] ++
          (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2)) ++
        [2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp
  have F6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2)) ++
        [3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3]) ++ ([0, 4, 2] ++ [2]) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [p6]; simp
  have F7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3]) ++ ([1, 0, 3] ++ [2]) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0]) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 5) 2 ++ [0])) ++ [] := by
    rw [p5]; simp
  have F8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0]) ++ ((3 : Sym) :: (List.replicate (2 * m + 8) 2 ++ [0])) ++
        [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0]) ++
        [0, 0, 3] ++ (List.replicate (2 * m + 8) 2 ++ [0]) := by
    simp
  have F9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0]) ++
        [0, 0, 4] ++ (List.replicate (2 * m + 8) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0]) ++
        [0, 0, 0] ++ ([4] ++ (List.replicate (2 * m + 8) 2 ++ [0])) := by
    simp
  have F10 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0]) ++
        [1, 2, 0] ++ ([4] ++ (List.replicate (2 * m + 8) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ([2, 0, 4] ++ [2]) ++ (List.replicate (2 * m + 7) 2 ++ [0]) := by
    rw [p8]; simp
  have F11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ([3, 1, 0] ++ [2]) ++ (List.replicate (2 * m + 7) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 1, 3, 1, 0]) ++ [2, 2] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    rw [p7]; simp
  have F12 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 1, 3, 1, 0]) ++ [3, 2] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 7) 2 ++ [0])) ++ [] := by
    rw [p7]; simp
  have F13 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 10) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 10) 2 ++ [0]) := by
    simp
  -- chain the stages
  have SP : Win St.B St.A (3 * r + 20) (3 * r + 15) _ _ 5 :=
    HP.cast (by simp; ring) (by simp; ring) F0.symm F1 rfl
  have SQ : Win St.A St.A (3 * r + 15) 12 _ _ (3 * r + 3) :=
    HQ.cast (by simp; ring) (by simp) rfl F2 (by ring)
  have SR : Win St.A St.A 12 10 _ _ 2 := HR.cast (by simp) (by simp) rfl F3 rfl
  have SS : Win St.A St.B 10 10 _ _ 4 := HS.cast (by simp) (by simp) rfl F4 rfl
  have ST : Win St.B St.B 10 (3 * r + 16) _ _ (3 * r + 6) :=
    HT.cast (by simp) (by simp; ring) rfl F5 (by ring)
  have SU : Win St.B St.A (3 * r + 16) (3 * r + 23) _ _ 7 :=
    HU.cast (by simp; ring) (by simp; ring) rfl F6 rfl
  have SV : Win St.A St.A (3 * r + 23) (3 * r + 26) _ _ 3 :=
    HV.cast (by simp; ring) (by simp; ring) rfl F7 rfl
  have SW : Win St.A St.A (3 * r + 26) (3 * r + 22) _ _ (10 * m + 34) :=
    HW.cast (by simp; ring) (by simp; ring) rfl F8 rfl
  have SX : Win St.A St.A (3 * r + 22) (3 * r + 20) _ _ 2 :=
    HX.cast (by simp; ring) (by simp; ring) rfl F9 rfl
  have SY : Win St.A St.B (3 * r + 20) (3 * r + 20) _ _ 4 :=
    HY.cast (by simp; ring) (by simp; ring) rfl F10 rfl
  have SZ : Win St.B St.B (3 * r + 20) (3 * r + 23) _ _ 3 :=
    HZ.cast (by simp; ring) (by simp; ring) rfl F11 rfl
  have SAA : Win St.B St.A (3 * r + 23) (3 * r + 24) _ _ 1 :=
    HAA.cast (by simp; ring) (by simp; ring) rfl F12 rfl
  have SBB : Win St.A St.A (3 * r + 24) (3 * r + 20) _ _ (10 * m + 44) :=
    HBB.cast (by simp; ring) (by simp; ring) rfl F13 rfl
  have U1 := SP.trans SQ (by simp)
  have U2 := U1.trans SR (by simp)
  have U3 := U2.trans SS (by simp)
  have U4 := U3.trans ST (by simp; omega)
  have U5 := U4.trans SU (by simp; omega)
  have U6 := U5.trans SV (by simp; omega)
  have U7 := U6.trans SW (by simp; omega)
  have U8 := U7.trans SX (by simp; omega)
  have U9 := U8.trans SY (by simp; omega)
  have U10 := U9.trans SZ (by simp; omega)
  have U11 := U10.trans SAA (by simp; omega)
  exact (U11.trans SBB (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The return to the left end -/

/-- **The return to the left end.**  The head crosses the whole region leftwards one last
time, rebuilds the prefix `U(2,2) u U(2,1)` and stops, in state `B`, on the new leftmost
non-blank cell, in exactly `22 + 3r` steps. -/
theorem p1fr_return (r m : ℕ) :
    Win St.A St.B (3 * r + 20) 0
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 10) 2 ++ [0]))
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 2 (2 * m + 10) ++
        [0])
      (22 + 3 * r) := by
  -- stage CC : the run of `2`s is left behind
  have HCC := fp1_backL.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1])
    (List.replicate (2 * m + 10) 2 ++ [0])
  -- stage DD : the run of `u`s crossed leftwards in state `B`
  have HDD := (Win.of_sweepL (sweepL_bulkB (r + 1)) 1).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0]
    ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0]))
  -- stage EE : one step
  have HEE := fp1_B1.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1]
    (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0])))
  -- stage FF : the last block
  have HFF := fp1_pre.embed (by simp) [0, 1, 3, 1]
    ([4] ++ (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0]))))
  -- stage GG : the closing
  have HGG := fp1_close.embed (by simp) []
    ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0]))))
  -- the tape words the computation passes through
  have G0 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 10) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [0, 3, 1, 0, 3, 1, 0, 1, 3] ++ (List.replicate (2 * m + 10) 2 ++ [0]) := by
    rw [show r + 2 = r + 1 + 1 from rfl, rep_succ', rep_succ']; simp
  have G1 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [0, 4, 2, 0, 4, 2, 0, 4, 4] ++
        (List.replicate (2 * m + 10) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ ((1 : Sym) :: rep [3, 1, 0] (r + 1)) ++
        ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have G2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ ((1 : Sym) :: rep [4, 2, 0] (r + 1)) ++
        ([4, 2, 0, 4, 2, 0, 4, 4] ++
          (List.replicate (2 * m + 10) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 1] ++
        (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0]))) := by
    simp
  have G3 : ([0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 4] ++
        (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++
            (List.replicate (2 * m + 10) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1] ++ [0, 0, 3, 1, 0] ++
        ([4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0])))) := by
    simp
  have G4 : ([0, 1, 3, 1] ++ [0, 0, 4, 2, 0] ++
        ([4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++
            (List.replicate (2 * m + 10) 2 ++ [0])))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0] ++
        ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 10) 2 ++ [0])))) := by
    simp
  have G5 : ([] ++ [0, 4, 4, 2, 2, 0] ++
        ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++
            (List.replicate (2 * m + 10) 2 ++ [0])))) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++
        tokU 2 (2 * m + 10) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl,
      show r + 2 = r + 1 + 1 from rfl, rep_succ']
    simp [tokU, rep_shift', rep_succ']
  -- chain the stages
  have SCC : Win St.A St.B (3 * r + 20) (3 * r + 12) _ _ 8 :=
    HCC.cast (by simp; ring) (by simp; ring) G0.symm G1 rfl
  have SDD : Win St.B St.B (3 * r + 12) 9 _ _ (3 * r + 3) :=
    HDD.cast (by simp; ring) (by simp) rfl G2 (by ring)
  have SEE : Win St.B St.B 9 8 _ _ 1 := HEE.cast (by simp) (by simp) rfl G3 rfl
  have SFF : Win St.B St.A 8 4 _ _ 4 := HFF.cast (by simp) (by simp) rfl G4 rfl
  have SGG : Win St.A St.B 4 0 _ _ 6 := HGG.cast (by simp) (by simp) rfl G5 rfl
  have V1 := SCC.trans SDD (by simp; omega)
  have V2 := V1.trans SEE (by simp; omega)
  have V3 := V2.trans SFF (by simp; omega)
  exact (V3.trans SGG (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The rule -/

/-- **The `P1` rule with an inner `U(2,2) V(1)`.**  The head is in state `B` on the
leftmost non-blank cell, with three blank cells to its left, and the tape reads

`U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · U(1,2m+2)`

followed by the `0` of the next token.  In exactly `237 + 12r + 40m` steps the machine
arrives, again in state `B`, on the new leftmost non-blank cell three cells further left,
the tape now reading `U(2,2) u · U(2,1) · u^(r+2) · U(2,2m+10)`.  Nothing outside the
window is read or written.

This is the row of the census in which the token that stops the carry is itself the left
end of a `P3` configuration; the head makes four passes instead of two. -/
theorem rule_P1_fractal (r m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++ tokV 1 ++
        tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 2 (2 * m + 10) ++
        [0])
      (237 + 12 * r + 40 * m) := by
  have h1 := (p1fr_pass12 r m).trans (p1fr_pass34 r m) (by simp; omega)
  have h2 := h1.trans (p1fr_return r m) (by simp; omega)
  exact h2.cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P1_fractal` is being applied. -/
theorem rule_P1_fractal_no_halt (r m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 237 + 12 * r + 40 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1_fractal r m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
