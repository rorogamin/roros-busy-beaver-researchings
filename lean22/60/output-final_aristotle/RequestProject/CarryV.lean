import RequestProject.CarryU2b

/-!
# The carry handed across a token `V`

The census of `ANALYSIS.md` §31 leaves two kinds of missing macro step: one in which the
token that absorbs the carry is `U(2,b)` (proved in `CarryU2b.lean`) and one in which a
token `V` follows the token the carry reaches.  This file proves the second, in the phase
`P3`:

```
0 0 0 · U(2,2) V(1) u · u^(r+1) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2) 0
          --(195 + 12r + 20m + 20c + 12s + 20m') steps-->
      U(2,1) U(4,1) · u^(r+1) · U(1,2m+6) · V(2c+1) · u^s · U(1,2m'+6) 0
```

So the carry is **not** absorbed by the first run of `2`s it meets: *both* tokens `U(1,·)`
gain four `2`s and the `V` gives up four.  (The short `V`s are the dangerous ones — `V(1)`
and `V(3)` in this position make the machine halt — which is why the rule is stated for
`V(2c+5)`.)

The mechanism is that a run of `2`s terminated by a `4` does not turn the head around: the
ping-pong marker `0 3` simply walks through the `4 3` that begins the `V` (the twelve-step
piece `vcross_step` below) and carries on through the `V`'s own run of `2`s, so that each
of the machine's two passes runs all the way to the last token.  Apart from `vcross_step`
and the two-step return `retV`, every piece of the proof is one that the earlier files
already provide; the computation is exhibited as thirty macro steps.
-/

namespace BB25

/-! ### The two new pieces -/

/-- **The ping-pong marker walks through a `V`.**  A run of `2`s terminated by a `4` does
not reflect the head: in twelve steps the marker `0 3` crosses the last `2` of the run and
the two cells `4 3` that begin the token `V`, and comes out on the `V`'s own run of `2`s
with the marker re-formed behind it. -/
theorem vcross_step : Win St.A St.A 2 6 [0, 3, 2, 4, 3, 2, 2] [1, 1, 0, 1, 0, 3, 2] 12 :=
  Win.of_lrun (by decide)

/-- **The two-step return at the far marker.**  Coming back leftwards in state `A` on the
`3` that a pass left at the right end, the head turns it into a `4` and steps over the `0`
next to it, arriving in state `A` on the cell to the left of the pair. -/
theorem retV : SweepL St.A St.A [0, 3] [0, 4] 2 := by
  have h := sweepL_A3.comp sweepL_B0 (by simp)
  norm_num at h
  exact h

/-! ### The rule -/

set_option maxHeartbeats 2000000 in
/-- **The `P3` rule with a `V` after the token the carry reaches.**  The head is in state
`B` on the leftmost non-blank cell, with three blank cells to its left, and the tape reads

`U(2,2) V(1) · u^(r+2) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2)`

followed by the `0` of the next token.  In exactly `195 + 12r + 20m + 20c + 12s + 20m'`
steps the machine hands the carry across the `V`: the token `U(1,2m+2)` becomes
`U(1,2m+6)`, the `V(2c+5)` becomes `V(2c+1)` and the last token becomes `U(1,2m'+6)`; the
head arrives, again in state `B`, on the new leftmost non-blank cell three cells further
left.  Nothing outside the window is read or written. -/
theorem rule_P3_V (r m c s mp : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 1 (2 * m + 2) ++
        tokV (2 * c + 5) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 1 (2 * m + 6) ++
        tokV (2 * c + 1) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 6) ++ [0])
      (195 + 12 * r + 20 * m + 20 * c + 12 * s + 20 * mp) := by
  -- splitting the runs
  have hz2m2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have hz2m3 : List.replicate (2 * m + 3) (2 : Sym)
      = [2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hz2m4 : List.replicate (2 * m + 4) (2 : Sym)
      = [2] ++ List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  have hz2c5 : List.replicate (2 * c + 5) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * c + 3) 2 := by
    rw [show 2 * c + 5 = 2 + (2 * c + 3) from by ring, replicate_split]; rfl
  have hz2c3 : List.replicate (2 * c + 3) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * c + 1) 2 := by
    rw [show 2 * c + 3 = 2 + (2 * c + 1) from by ring, replicate_split]; rfl
  have hzmp2 : List.replicate (2 * mp + 2) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 2 = 2 + 2 * mp from by ring, replicate_split]; rfl
  have hzmp1 : List.replicate (2 * mp + 1) (2 : Sym)
      = [2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 1 = 1 + 2 * mp from by ring, replicate_split]; rfl
  have hzmp4 : List.replicate (2 * mp + 4) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * mp + 2) 2 := by
    rw [show 2 * mp + 4 = 2 + (2 * mp + 2) from by ring, replicate_split]; rfl
  have hzmp3 : List.replicate (2 * (mp + 1) + 1) (2 : Sym)
      = [2] ++ List.replicate (2 * mp + 2) 2 := by
    rw [show 2 * (mp + 1) + 1 = 1 + (2 * mp + 2) from by ring, replicate_split]; rfl
  have ho2c5 : List.replicate (2 * c + 5) (1 : Sym)
      = [1] ++ (List.replicate (2 * c + 2) 1 ++ [1, 1]) := by
    rw [show 2 * c + 5 = 1 + ((2 * c + 2) + 2) from by ring, replicate_split, replicate_split]
    rfl
  have ho2c3 : List.replicate (2 * c + 3) (1 : Sym)
      = [1] ++ (List.replicate (2 * c) 1 ++ [1, 1]) := by
    rw [show 2 * c + 3 = 1 + ((2 * c) + 2) from by ring, replicate_split, replicate_split]
    rfl
  have ho2m4 : List.replicate (2 * m + 4) (1 : Sym)
      = [1] ++ (List.replicate (2 * m) 1 ++ [1, 1, 1]) := by
    rw [show 2 * m + 4 = 1 + ((2 * m) + 3) from by ring, replicate_split, replicate_split]
    rfl
  have ho2m6 : List.replicate (2 * m + 6) (1 : Sym)
      = [1] ++ (List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) := by
    rw [show 2 * m + 6 = 1 + ((2 * m + 2) + 3) from by ring, replicate_split, replicate_split]
    rfl
  have hz2m1 : List.replicate (2 * m + 1) (2 : Sym) = [2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  have hrep3 : rep ([0, 4, 2] : List Sym) (r + 1 + 1 + 1)
      = [0, 4, 2] ++ (rep [0, 4, 2] (r + 1) ++ [0, 4, 2]) := by
    rw [rep_succ, rep_succ']
  have Etail : (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))
        : List Sym)
      = 0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [rep_shift']; simp
  -- the thirty stages
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] (r + 1) ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
        (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))))
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1 + 1 + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  have HC1 := (pingpong_chain0 m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1])
    ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))
  have HC2 := vcross_step.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1)
    (List.replicate (2 * c + 3) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have HC3 := (pingpong_chain0 (c + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1])
    ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have HC4 := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1)
    (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))
  have HD := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp) 2 ++ [0])
  have HE := (cross_back mp).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0] ++
      rep [3, 1, 0] s) []
  have HF := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 4) 2 ++ [0])
  have HG := (Win.of_sweepL retV 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1])
    (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
  have HH := (Win.of_sweepL (run_ones_A (2 * c + 5)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1])
    ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have HI := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1])
    (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HJ := (Win.of_sweepL (run_ones_A (2 * m + 4)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0])
    ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
  have HL := (Win.of_sweepL (sweepL_bulk (r + 1 + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HM := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))))
  have HN := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1 + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HO := carry_B2.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1 + 1))
    (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HP := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1])
    ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
  have HQ := vcross_step.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1)
    (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HR := (pingpong_chain0 c).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1])
    ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HS := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1)
    ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have HT := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp + 2) 2 ++ [0])
  have HU := (cross_back (mp + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0] ++
      rep [3, 1, 0] s) []
  have HV := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 6) 2 ++ [0])
  have HW := (Win.of_sweepL retV 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1])
    (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
  have HX := (Win.of_sweepL (run_ones_A (2 * c + 3)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1])
    ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
  have HY := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1])
    (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))
  have HZ := (Win.of_sweepL (run_ones_A (2 * m + 6)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1))
    ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have HAA := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
  have HAB := p3_final.embed (by simp) []
    (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
      (List.replicate (2 * c + 1) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 2) ++
        tokU 1 (2 * m + 2) ++ tokV (2 * c + 5) ++ rep (tokU 1 1) s ++
        tokU 1 (2 * mp + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] (r + 1) ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
            (rep [0, 4, 2] s ++ ([0, 4] ++
              (List.replicate (2 * mp + 2) 2 ++ [0]))))))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl,
      show r + 2 = (r + 1) + 1 from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] (r + 1) ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
            (rep [0, 4, 2] s ++ ([0, 4] ++
              (List.replicate (2 * mp + 2) 2 ++ [0]))))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 1 + 1 + 1) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    rw [hrep3, hz2m2]; simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 1 + 1 + 1) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0])))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1]) ++
        ([0, 3] ++ List.replicate (2 * m + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) (r + 1 + 1), hz2m1]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1]) ++
        (List.replicate (2 * m) 1 ++ [0, 3, 2]) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1) ++ [0, 3, 2, 4, 3, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1) ++ [1, 1, 0, 1, 0, 3, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * c + 3) 2) ++
        ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++
          (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    simpa using replicate_cons_comm 2 (2 * c + 3) _
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        (List.replicate (2 * c + 2) 1 ++ [0, 3, 2]) ++
        ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++
          (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1) ++
        [0, 3, 2, 2, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [Etail]; simp
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1) ++
        [1, 1, 0, 3, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) := by
    rw [rep_succ' ([0, 4, 2] : List Sym) s, hzmp2]; simp [rep_shift']
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * mp + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ ([1, 0, 3] : List Sym) s, hzmp1]; simp [rep_shift']
  have E8 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        (3 :: (List.replicate (2 * mp + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0]) ++ (3 :: rep [1, 0, 3] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) := by
    simp [rep_shift']
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0]) ++ (3 :: rep [2, 0, 4] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1]) ++
        [1, 0, 3] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])) := by
    simp
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1]) ++
        [1, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ (0 :: List.replicate (2 * c + 5) 1) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    rw [ho2c5]; simp
  have E11 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ (0 :: List.replicate (2 * c + 5) 2) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ [0, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E12 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1 + 1) ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ [1, 4, 3] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        (3 :: List.replicate (2 * m + 4) 1) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) (r + 1), ho2m4]; simp
  have E13 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        (3 :: List.replicate (2 * m + 4) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
          : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1 + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) (r + 1)]; simp
  have E14 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1 + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 4) 2 ++ [0])))))))) := by
    rw [rep_succ ([2, 0, 4] : List Sym) (r + 1)]; simp
  have E15 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 4) 2 ++ [0])))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1 + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    rw [rep_succ ([2, 0, 4] : List Sym) (r + 1), hz2m4]; simp
  have E16 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1 + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1 + 1)) ++ [2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    rw [hz2m3]; simp
  have E17 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1 + 1)) ++ [3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1]) ++
        ([0, 3] ++ List.replicate (2 * (m + 1) + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    rw [rep_succ' ([3, 1, 0] : List Sym) (r + 1),
      show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, hz2m3]
    simp
  have E18 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1]) ++
        (List.replicate (2 * (m + 1)) 1 ++ [0, 3, 2]) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1) ++ [0, 3, 2, 4, 3, 2, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, hz2c3]; simp
  have E19 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1) ++ [1, 1, 0, 1, 0, 3, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * c + 1) 2) ++
        ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    simpa using replicate_cons_comm 2 (2 * c + 1) _
  have E20 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1]) ++
        (List.replicate (2 * c) 1 ++ [0, 3, 2]) ++
        ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1) ++
        [0, 3, 2, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    simp
  have E21 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1) ++
        [1, 1, 0, 3, 0] ++
        ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp + 2) 2 ++ [0]) := by
    rw [rep_succ' ([0, 4, 2] : List Sym) s, hzmp4]; simp [rep_shift']
  have E22 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (mp + 1) + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ ([1, 0, 3] : List Sym) s, hzmp3]; simp [rep_shift']
  have E23 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        (3 :: (List.replicate (2 * (mp + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0]) ++ (3 :: rep [1, 0, 3] s) ++
        (List.replicate (2 * mp + 6) 2 ++ [0]) := by
    rw [show 2 * (mp + 1) + 4 = 2 * mp + 6 from by ring]; simp [rep_shift']
  have E24 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0]) ++ (3 :: rep [2, 0, 4] s) ++
        (List.replicate (2 * mp + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1]) ++
        [1, 0, 3] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])) := by
    simp
  have E25 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1]) ++
        [1, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: List.replicate (2 * c + 3) 1) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))) := by
    rw [ho2c3]; simp
  have E26 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: List.replicate (2 * c + 3) 2) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++ [0, 2, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))) := by
    rw [hz2c3]; simp
  have E27 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1) ++ [3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++ [1, 4, 3] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++
        (3 :: List.replicate (2 * m + 6) 1) ++
        ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    rw [ho2m6]; simp
  have E28 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++
        (3 :: List.replicate (2 * m + 6) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
          : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))) := by
    simp [rep_shift']
  have E29 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
          : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 1) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 6) 2 ++ [0]))))))) := by
    simp
  have E30 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 1) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 6) 2 ++ [0]))))))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 1 (2 * m + 6) ++
        tokV (2 * c + 1) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 6) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * r + 20) _ _ (3 * r + 9) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC1 : Win St.A St.A (3 * r + 20) (3 * r + 2 * m + 20) _ _ (8 * m) :=
    HC1.cast (by simp; omega) (by simp; omega) rfl E3 rfl
  have SC2 : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 2 * m + 24) _ _ 12 :=
    HC2.cast (by simp; omega) (by simp; omega) rfl E4 rfl
  have SC3 : Win St.A St.A (3 * r + 2 * m + 24) (3 * r + 2 * m + 2 * c + 26) _ _
      (8 * c + 8) :=
    HC3.cast (by simp; omega) (by simp; omega) rfl E5 (by ring)
  have SC4 : Win St.A St.A (3 * r + 2 * m + 2 * c + 26) (3 * r + 2 * m + 2 * c + 28) _ _ 8 :=
    HC4.cast (by simp; omega) (by simp; omega) rfl E6 rfl
  have SD : Win St.A St.A (3 * r + 2 * m + 2 * c + 28)
      (3 * r + 2 * m + 2 * c + 3 * s + 31) _ _ (3 * s + 3) :=
    HD.cast (by simp; omega) (by simp; omega) rfl E7 (by ring)
  have SE : Win St.A St.A (3 * r + 2 * m + 2 * c + 3 * s + 31)
      (3 * r + 2 * m + 2 * c + 3 * s + 27) _ _ (10 * mp + 14) :=
    HE.cast (by simp; omega) (by simp; omega) rfl E8 rfl
  have SF : Win St.A St.A (3 * r + 2 * m + 2 * c + 3 * s + 27)
      (3 * r + 2 * m + 2 * c + 27) _ _ (3 * s) :=
    HF.cast (by simp; omega) (by simp; omega) rfl E9 (by ring)
  have SG : Win St.A St.A (3 * r + 2 * m + 2 * c + 27) (3 * r + 2 * m + 2 * c + 25) _ _ 2 :=
    HG.cast (by simp; omega) (by simp; omega) rfl E10 rfl
  have SH : Win St.A St.A (3 * r + 2 * m + 2 * c + 25) (3 * r + 2 * m + 20) _ _
      (2 * c + 5) :=
    HH.cast (by simp; omega) (by simp; omega) rfl E11 rfl
  have SI : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 2 * m + 20) _ _ 4 :=
    HI.cast (by simp; omega) (by simp; omega) rfl E12 rfl
  have SJ : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 16) _ _ (2 * m + 4) :=
    HJ.cast (by simp; omega) (by simp; omega) rfl E13 rfl
  have SL : Win St.A St.A (3 * r + 16) 10 _ _ (3 * r + 6) :=
    HL.cast (by simp; omega) (by simp) rfl E14 (by ring)
  have SM : Win St.A St.B 10 11 _ _ 7 :=
    HM.cast (by simp) (by simp) rfl E15 rfl
  have SN : Win St.B St.B 11 (3 * r + 17) _ _ (3 * r + 6) :=
    HN.cast (by simp) (by simp; ring) rfl E16 (by ring)
  have SO : Win St.B St.A (3 * r + 17) (3 * r + 18) _ _ 1 :=
    HO.cast (by simp; omega) (by simp; omega) rfl E17 rfl
  have SP : Win St.A St.A (3 * r + 18) (3 * r + 2 * m + 20) _ _ (8 * m + 8) :=
    HP.cast (by simp; omega) (by simp; omega) rfl E18 (by ring)
  have SQ : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 2 * m + 24) _ _ 12 :=
    HQ.cast (by simp; omega) (by simp; omega) rfl E19 rfl
  have SR : Win St.A St.A (3 * r + 2 * m + 24) (3 * r + 2 * m + 2 * c + 24) _ _ (8 * c) :=
    HR.cast (by simp; omega) (by simp; omega) rfl E20 rfl
  have SS : Win St.A St.A (3 * r + 2 * m + 2 * c + 24) (3 * r + 2 * m + 2 * c + 26) _ _ 8 :=
    HS.cast (by simp; omega) (by simp; omega) rfl E21 rfl
  have ST : Win St.A St.A (3 * r + 2 * m + 2 * c + 26)
      (3 * r + 2 * m + 2 * c + 3 * s + 29) _ _ (3 * s + 3) :=
    HT.cast (by simp; omega) (by simp; omega) rfl E22 (by ring)
  have SU : Win St.A St.A (3 * r + 2 * m + 2 * c + 3 * s + 29)
      (3 * r + 2 * m + 2 * c + 3 * s + 25) _ _ (10 * mp + 24) :=
    HU.cast (by simp; omega) (by simp; omega) rfl E23 (by ring)
  have SV : Win St.A St.A (3 * r + 2 * m + 2 * c + 3 * s + 25)
      (3 * r + 2 * m + 2 * c + 25) _ _ (3 * s) :=
    HV.cast (by simp; omega) (by simp; omega) rfl E24 (by ring)
  have SW : Win St.A St.A (3 * r + 2 * m + 2 * c + 25) (3 * r + 2 * m + 2 * c + 23) _ _ 2 :=
    HW.cast (by simp; omega) (by simp; omega) rfl E25 rfl
  have SX : Win St.A St.A (3 * r + 2 * m + 2 * c + 23) (3 * r + 2 * m + 20) _ _
      (2 * c + 3) :=
    HX.cast (by simp; omega) (by simp; omega) rfl E26 rfl
  have SY : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 2 * m + 20) _ _ 4 :=
    HY.cast (by simp; omega) (by simp; omega) rfl E27 rfl
  have SZ : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 14) _ _ (2 * m + 6) :=
    HZ.cast (by simp; omega) (by simp; omega) rfl E28 rfl
  have SAA : Win St.A St.A (3 * r + 14) 11 _ _ (3 * r + 3) :=
    HAA.cast (by simp; omega) (by simp) rfl E29 (by ring)
  have SAB : Win St.A St.B 11 0 _ _ 11 :=
    HAB.cast (by simp) (by simp) rfl E30 rfl
  have T1 := SA.trans SB (by simp; omega)
  have T2 := T1.trans SC1 (by simp; omega)
  have T3 := T2.trans SC2 (by simp; omega)
  have T4 := T3.trans SC3 (by simp; omega)
  have T5 := T4.trans SC4 (by simp; omega)
  have T6 := T5.trans SD (by simp; omega)
  have T7 := T6.trans SE (by simp; omega)
  have T8 := T7.trans SF (by simp; omega)
  have T9 := T8.trans SG (by simp; omega)
  have T10 := T9.trans SH (by simp; omega)
  have T11 := T10.trans SI (by simp; omega)
  have T12 := T11.trans SJ (by simp; omega)
  have T13 := T12.trans SL (by simp; omega)
  have T14 := T13.trans SM (by simp; omega)
  have T15 := T14.trans SN (by simp; omega)
  have T16 := T15.trans SO (by simp; omega)
  have T17 := T16.trans SP (by simp; omega)
  have T18 := T17.trans SQ (by simp; omega)
  have T19 := T18.trans SR (by simp; omega)
  have T20 := T19.trans SS (by simp; omega)
  have T21 := T20.trans ST (by simp; omega)
  have T22 := T21.trans SU (by simp; omega)
  have T23 := T22.trans SV (by simp; omega)
  have T24 := T23.trans SW (by simp; omega)
  have T25 := T24.trans SX (by simp; omega)
  have T26 := T25.trans SY (by simp; omega)
  have T27 := T26.trans SZ (by simp; omega)
  have T28 := T27.trans SAA (by simp; omega)
  exact (T28.trans SAB (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_V` is being applied. -/
theorem rule_P3_V_no_halt (r m c s mp : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 2) ++
      tokU 1 (2 * m + 2) ++ tokV (2 * c + 5) ++ rep (tokU 1 1) s ++
      tokU 1 (2 * mp + 2) ++ [0])) :
    ∀ i ≤ 195 + 12 * r + 20 * m + 20 * c + 12 * s + 20 * mp,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_V r m c s mp).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
