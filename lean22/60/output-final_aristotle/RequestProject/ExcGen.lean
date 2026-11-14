import RequestProject.FracP1s

/-!
# The three general excursions

A *carry excursion* is what the head does when, standing just left of a run of tokens
`u = U(1,1)`, it runs right along the run, is turned around by the token beyond it and
comes back to where it started.  Reading the five excursions of the `P3` row of
`U2bV.lean` side by side shows that they are instances of only **three** window rules,
each with its own pair of parameters: the length of the run of `u`s and the length of the
run of `2`s beyond it.  This file proves the three in that general form.

Writing `(abc)^n` for `rep [a,b,c] n`, the three are

```
exc_A042 k m : A, offset 1 -> A, offset 0,  6k + 10m + 17 steps
    [3] ++ (042)^(k+1) ++ 2^(2m+1) ++ [0]  ->  [3] ++ (204)^k ++ 2^(2m+4) ++ [0]
exc_B204 k m : B, offset 1 -> B, offset 0,  6k + 10m + 29 steps
    [0] ++ (204)^(k+1) ++ 2^(2m+4) ++ [0]  ->  [0] ++ (420)^k ++ [4] ++ 2^(2m+6) ++ [0]
exc_C420 k m : B, offset 1 -> A, offset 0,  6k + 10m + 41 steps
    [1] ++ (420)^(k+1) ++ [4] ++ 2^(2m+6) ++ [0]  ->  [1] ++ (042)^(k+1) ++ 2^(2m+7) ++ [0]
```

In `exc_A042` and `exc_B204` the run of `u`s loses one token and the run of `2`s grows;
in `exc_C420` the run keeps its length and only the `2`s grow.  Applied in the cyclic
order `A, B, C, A, B, C, …` they describe a whole sequence of passes over one and the same
region — which is exactly what the rows of the census with many passes need.

Each proof is a chain of the sweeps, ping-pongs and turn-arounds the development already
provides, and none of them looks at the tape left of the cell where it starts.
-/

namespace BB25

/-! ### Three small pieces -/

/-- Shifting the window of a `3`-periodic run by two cells. -/
lemma rep_shift2 (a b c : Sym) (k : ℕ) (t : List Sym) :
    a :: b :: (rep [c, a, b] k ++ t) = rep [a, b, c] k ++ (a :: b :: t) := by
  rw [rep_shift' b c a k, rep_shift' a b c k]

/-- Two steps: in state `B` on the `4` of a token `U(1,b)` whose `2`-run follows, the head
writes `0 3` and stops on the second `2`. -/
theorem exc_two42 : Win St.B St.A 0 2 [4, 2, 2] [0, 3, 2] 2 :=
  Win.of_lrun (by decide)

/-- One step: in state `A` on a `3`, write `4` and step left onto an untouched cell. -/
theorem exc_one3 : Win St.A St.B 1 0 [0, 3] [0, 4] 1 :=
  Win.of_lrun (by decide)

/-- Two steps: the head crosses the `3` at the left end of a swept block and stops on the
`0` beyond it, with a `1` to the left of that. -/
theorem exc_two103 : Win St.A St.A 2 0 [1, 0, 3] [1, 0, 4] 2 :=
  Win.of_lrun (by decide)

/-! ### The excursion that is absorbed by the run of `2`s -/

/-- **Excursion `A`.**  Entering a run of `k+1` tokens `u` in state `A` from the `3` at its
left end, the head crosses the run, is absorbed by the odd run of `2`s beyond it and comes
straight back. -/
theorem exc_A042 (k m : ℕ) :
    Win St.A St.A 1 0
      ([3] ++ rep [0, 4, 2] (k + 1) ++ (List.replicate (2 * m + 1) 2 ++ [0]))
      ([3] ++ rep [2, 0, 4] k ++ (List.replicate (2 * m + 4) 2 ++ [0]))
      (6 * k + 10 * m + 17) := by
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split (2 : Sym) 1 (2 * m)]; rfl
  -- stage A : the rightward sweep
  have HA := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (k + 1)) (by simp) 2).embed
    (by simp) [3] (List.replicate (2 * m) 2 ++ [0])
  -- stage B : the round trip through the run of `2`s
  have HB := (cross_back m).embed (by simp) (rep [3, 1, 0] k) []
  -- stage C : the leftward sweep back
  have HC := (Win.of_sweepL (sweepL_bulk k) 3).embed (by simp) []
    (List.replicate (2 * m + 4) 2 ++ [0])
  have E0 : ([3] ++ rep [0, 4, 2] (k + 1) ++
        (List.replicate (2 * m + 1) 2 ++ [0]) : List Sym)
      = [3] ++ (rep [0, 4, 2] (k + 1) ++ [2]) ++ (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q1]; simp
  have E1 : ([3] ++ (rep [1, 0, 3] (k + 1) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = rep [3, 1, 0] k ++ ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [q1]
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.append_nil]
    rw [rep_shift' 3 1 0 (k + 1), rep_succ' (w := [3, 1, 0]) k]
    simp
  have E2 : (rep [3, 1, 0] k ++ (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ []
        : List Sym)
      = [] ++ ((3 : Sym) :: rep [1, 0, 3] k) ++ (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp [rep_shift' 3 1 0 k]
  have E3 : ([] ++ ((3 : Sym) :: rep [2, 0, 4] k) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = [3] ++ rep [2, 0, 4] k ++ (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp
  have SA : Win St.A St.A 1 (3 * k + 4) _ _ (3 * k + 3) :=
    HA.cast (by simp) (by simp; omega) E0.symm E1 (by ring)
  have SB : Win St.A St.A (3 * k + 4) (3 * k) _ _ (10 * m + 14) :=
    HB.cast (by simp; omega) (by simp; ring) rfl E2 rfl
  have SC : Win St.A St.A (3 * k) 0 _ _ (3 * k) :=
    HC.cast (by simp; ring) (by simp) rfl E3 (by ring)
  have U1 := SA.trans SB (by simp; omega)
  exact (U1.trans SC (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The excursion that passes the carry on inside the run of `2`s -/

/-- **Excursion `B`.**  Entering a run of `k+1` tokens `u` in state `B` from the `0` at its
left end, the head crosses the run, ping-pongs through the even run of `2`s beyond it and
comes back. -/
theorem exc_B204 (k m : ℕ) :
    Win St.B St.B 1 0
      ([0] ++ rep [2, 0, 4] (k + 1) ++ (List.replicate (2 * m + 4) 2 ++ [0]))
      ([0] ++ rep [4, 2, 0] k ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      (6 * k + 10 * m + 29) := by
  have q4 : List.replicate (2 * m + 4) (2 : Sym) = 2 :: List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 3)]; rfl
  have q3 : List.replicate (2 * m + 3) (2 : Sym) = 2 :: List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 2)]; rfl
  -- stage A : the rightward sweep in state `B`
  have HA := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (k + 1)) (by simp) 2).embed
    (by simp) [0] (List.replicate (2 * m + 3) 2 ++ [0])
  -- stage B : one step into the run of `2`s
  have HB := carry_B2.embed (by simp) ([0] ++ rep [3, 1, 0] (k + 1))
    (List.replicate (2 * m + 2) 2 ++ [0])
  -- stage C : the ping-pong through the run of `2`s
  have HC := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0] ++ rep [3, 1, 0] k ++ [3, 1]) [0]
  -- stage D : the turn-around at the far end
  have HD := rule_endgame.embed (by simp)
    ([0] ++ rep [3, 1, 0] k ++ [3, 1] ++ List.replicate (2 * m + 2) 1) []
  -- stage E : the return sweep over the run of `1`s
  have HE := (onesBack_gen 3 (2 * m + 6)).embed (by simp) ([0] ++ rep [3, 1, 0] k) []
  -- stage F : the leftward sweep back
  have HF := (Win.of_sweepL (sweepL_bulk k) 3).embed (by simp) [0]
    (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage G : the last step out of the region
  have HG := exc_one3.embed (by simp) []
    (rep [2, 0, 4] k ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  have E0 : ([0] ++ rep [2, 0, 4] (k + 1) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = [0] ++ (rep [2, 0, 4] (k + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) := by
    rw [q4]; simp
  have E1 : ([0] ++ (rep [3, 1, 0] (k + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) : List Sym)
      = ([0] ++ rep [3, 1, 0] (k + 1)) ++ [2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [q3]; simp
  have E2 : (([0] ++ rep [3, 1, 0] (k + 1)) ++ [3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0] ++ rep [3, 1, 0] k ++ [3, 1]) ++
        ([0, 3] ++ List.replicate (2 * m + 3) 2) ++ [0] := by
    rw [q3, rep_succ' (w := [3, 1, 0]) k]; simp
  have E3 : (([0] ++ rep [3, 1, 0] k ++ [3, 1]) ++
        (List.replicate (2 * m + 2) 1 ++ [0, 3, 2]) ++ [0] : List Sym)
      = ([0] ++ rep [3, 1, 0] k ++ [3, 1] ++ List.replicate (2 * m + 2) 1) ++
        [0, 3, 2, 0] ++ [] := by
    simp
  have E4 : (([0] ++ rep [3, 1, 0] k ++ [3, 1] ++ List.replicate (2 * m + 2) 1) ++
        [1, 1, 1, 0] ++ [] : List Sym)
      = ([0] ++ rep [3, 1, 0] k) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 1 ++ [0])) ++ [] := by
    have e : List.replicate (2 * m + 6) (1 : Sym)
        = 1 :: (List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) := by
      rw [show 2 * m + 6 = 1 + ((2 * m + 2) + 3) from by ring,
        replicate_split (1 : Sym) 1 ((2 * m + 2) + 3),
        replicate_split (1 : Sym) (2 * m + 2) 3]
      rfl
    rw [e]; simp
  have E5 : (([0] ++ rep [3, 1, 0] k) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 2 ++ [0])) ++ [] : List Sym)
      = [0] ++ ((3 : Sym) :: rep [1, 0, 3] k) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp [rep_shift' 3 1 0 k]
  have E6 : ([0] ++ ((3 : Sym) :: rep [2, 0, 4] k) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = [] ++ [0, 3] ++ (rep [2, 0, 4] k ++
        (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp
  have E7 : ([] ++ [0, 4] ++ (rep [2, 0, 4] k ++
        (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [0] ++ rep [4, 2, 0] k ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp [rep_shift' 4 2 0 k]
  have SA : Win St.B St.B 1 (3 * k + 4) _ _ (3 * k + 3) :=
    HA.cast (by simp) (by simp; ring) E0.symm E1 (by ring)
  have SB : Win St.B St.A (3 * k + 4) (3 * k + 5) _ _ 1 :=
    HB.cast (by simp; ring) (by simp; ring) rfl E2 rfl
  have SC : Win St.A St.A (3 * k + 5) (3 * k + 2 * m + 7) _ _ (8 * m + 8) :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 (by ring)
  have SD : Win St.A St.B (3 * k + 2 * m + 7) (3 * k + 2 * m + 8) _ _ 9 :=
    HD.cast (by simp; ring) (by simp; ring) rfl E4 rfl
  have SE : Win St.B St.A (3 * k + 2 * m + 8) (3 * k + 1) _ _ (2 * m + 7) :=
    HE.cast (by simp; ring) (by simp; ring) rfl E5 (by ring)
  have SF : Win St.A St.A (3 * k + 1) 1 _ _ (3 * k) :=
    HF.cast (by simp; ring) (by simp) rfl E6 (by ring)
  have SG : Win St.A St.B 1 0 _ _ 1 :=
    HG.cast (by simp) (by simp) rfl E7 rfl
  have U1 := SA.trans SB (by simp)
  have U2 := U1.trans SC (by simp; omega)
  have U3 := U2.trans SD (by simp; omega)
  have U4 := U3.trans SE (by simp; omega)
  have U5 := U4.trans SF (by simp; omega)
  exact (U5.trans SG (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The excursion that keeps the length of the run -/

/-- **Excursion `C`.**  Entering a run of `k+1` tokens `u` in state `B` from the `1` at its
left end, with a spare `4` between the run and the even run of `2`s, the head crosses the
run, ping-pongs through the `2`s and comes back; the spare `4` is absorbed into the run, so
the run keeps its length. -/
theorem exc_C420 (k m : ℕ) :
    Win St.B St.A 1 0
      ([1] ++ rep [4, 2, 0] (k + 1) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      ([1] ++ rep [0, 4, 2] (k + 1) ++ (List.replicate (2 * m + 7) 2 ++ [0]))
      (6 * k + 10 * m + 41) := by
  have q6 : List.replicate (2 * m + 6) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * m + 4) 2 := by
    rw [show 2 * m + 6 = 2 + (2 * m + 4) from by ring,
      replicate_split (2 : Sym) 2 (2 * m + 4)]; rfl
  have q8 : List.replicate (2 * m + 8) (2 : Sym) = 2 :: List.replicate (2 * m + 7) 2 := by
    rw [show 2 * m + 8 = 1 + (2 * m + 7) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 7)]; rfl
  -- stage A : the rightward sweep in state `B`
  have HA := (Win.of_sweepR (sweepR_rep sweepR_420 (by simp) (k + 1)) (by simp) 4).embed
    (by simp) [1] (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage B : the two steps that open the run of `2`s
  have HB := exc_two42.embed (by simp) ([1] ++ rep [0, 3, 1] (k + 1))
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage C : the ping-pong through the run of `2`s
  have HC := (pingpong_chain0 (m + 2)).embed (by simp)
    ([1] ++ rep [0, 3, 1] (k + 1)) [0]
  -- stage D : the turn-around at the far end
  have HD := rule_endgame.embed (by simp)
    ([1] ++ rep [0, 3, 1] (k + 1) ++ List.replicate (2 * m + 4) 1) []
  -- stage E : the return sweep over the run of `1`s
  have HE := (onesBack_gen 3 (2 * m + 8)).embed (by simp)
    ([1] ++ rep [0, 3, 1] k ++ [0]) []
  -- stage F : the leftward sweep back
  have HF := (Win.of_sweepL (sweepL_bulk k) 3).embed (by simp) [1, 0]
    (List.replicate (2 * m + 8) 2 ++ [0])
  -- stage G : the last two steps out of the region
  have HG := exc_two103.embed (by simp) []
    (rep [2, 0, 4] k ++ (List.replicate (2 * m + 8) 2 ++ [0]))
  have E0 : ([1] ++ rep [4, 2, 0] (k + 1) ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [1] ++ (rep [4, 2, 0] (k + 1) ++ [4]) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp
  have E1 : ([1] ++ (rep [0, 3, 1] (k + 1) ++ [4]) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = ([1] ++ rep [0, 3, 1] (k + 1)) ++ [4, 2, 2] ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [q6]; simp
  have E2 : (([1] ++ rep [0, 3, 1] (k + 1)) ++ [0, 3, 2] ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([1] ++ rep [0, 3, 1] (k + 1)) ++
        ([0, 3] ++ List.replicate (2 * m + 5) 2) ++ [0] := by
    rw [show 2 * m + 5 = 1 + (2 * m + 4) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 4)]; simp
  have E3 : (([1] ++ rep [0, 3, 1] (k + 1)) ++
        (List.replicate (2 * m + 4) 1 ++ [0, 3, 2]) ++ [0] : List Sym)
      = ([1] ++ rep [0, 3, 1] (k + 1) ++ List.replicate (2 * m + 4) 1) ++
        [0, 3, 2, 0] ++ [] := by
    simp
  have E4 : (([1] ++ rep [0, 3, 1] (k + 1) ++ List.replicate (2 * m + 4) 1) ++
        [1, 1, 1, 0] ++ [] : List Sym)
      = ([1] ++ rep [0, 3, 1] k ++ [0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 8) 1 ++ [0])) ++ [] := by
    have e : List.replicate (2 * m + 8) (1 : Sym)
        = 1 :: (List.replicate (2 * m + 4) 1 ++ [1, 1, 1]) := by
      rw [show 2 * m + 8 = 1 + ((2 * m + 4) + 3) from by ring,
        replicate_split (1 : Sym) 1 ((2 * m + 4) + 3),
        replicate_split (1 : Sym) (2 * m + 4) 3]
      rfl
    rw [e, rep_succ' (w := [0, 3, 1]) k]; simp
  have E5 : (([1] ++ rep [0, 3, 1] k ++ [0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 8) 2 ++ [0])) ++ [] : List Sym)
      = [1, 0] ++ ((3 : Sym) :: rep [1, 0, 3] k) ++
        (List.replicate (2 * m + 8) 2 ++ [0]) := by
    simp [rep_shift2 0 3 1 k]
  have E6 : ([1, 0] ++ ((3 : Sym) :: rep [2, 0, 4] k) ++
        (List.replicate (2 * m + 8) 2 ++ [0]) : List Sym)
      = [] ++ [1, 0, 3] ++ (rep [2, 0, 4] k ++
        (List.replicate (2 * m + 8) 2 ++ [0])) := by
    simp
  have E7 : ([] ++ [1, 0, 4] ++ (rep [2, 0, 4] k ++
        (List.replicate (2 * m + 8) 2 ++ [0])) : List Sym)
      = [1] ++ rep [0, 4, 2] (k + 1) ++ (List.replicate (2 * m + 7) 2 ++ [0]) := by
    rw [q8, rep_succ' (w := [0, 4, 2]) k]
    simp [rep_shift2 0 4 2 k]
  have SA : Win St.B St.B 1 (3 * k + 4) _ _ (3 * k + 3) :=
    HA.cast (by simp) (by simp; ring) E0.symm E1 (by ring)
  have SB : Win St.B St.A (3 * k + 4) (3 * k + 6) _ _ 2 :=
    HB.cast (by simp; ring) (by simp; ring) rfl E2 rfl
  have SC : Win St.A St.A (3 * k + 6) (3 * k + 2 * m + 10) _ _ (8 * m + 16) :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 (by ring)
  have SD : Win St.A St.B (3 * k + 2 * m + 10) (3 * k + 2 * m + 11) _ _ 9 :=
    HD.cast (by simp; ring) (by simp; ring) rfl E4 rfl
  have SE : Win St.B St.A (3 * k + 2 * m + 11) (3 * k + 2) _ _ (2 * m + 9) :=
    HE.cast (by simp; ring) (by simp; ring) rfl E5 (by ring)
  have SF : Win St.A St.A (3 * k + 2) 2 _ _ (3 * k) :=
    HF.cast (by simp; ring) (by simp) rfl E6 (by ring)
  have SG : Win St.A St.A 2 0 _ _ 2 :=
    HG.cast (by simp) (by simp) rfl E7 rfl
  have U1 := SA.trans SB (by simp)
  have U2 := U1.trans SC (by simp)
  have U3 := U2.trans SD (by simp)
  have U4 := U3.trans SE (by simp; omega)
  have U5 := U4.trans SF (by simp; omega)
  exact (U5.trans SG (by simp; omega)).cast rfl rfl rfl rfl (by ring)

end BB25
