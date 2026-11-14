import RequestProject.FracP1

/-!
# The `P1` fractal row with intervening tokens

`FracP1.lean` proves the `P1` row of the census in which the absorbing token comes
immediately after the inner `U(2,2) V(1) u`.  This file proves the variant in which a run
of `s+1` further tokens `u` separates them:

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · u^(s+1) · U(1,2m+2) 0
       --(261 + 12r + 24s + 40m) steps-->
   U(2,2) u · U(2,1) · u^(r+2) · U(2,1) · u^s · U(1,2m+10) 0
```

The computation has the same shape as `rule_P1_fractal` — four passes, turned around twice
by the inner `P3` prefix — with the run of `s+1` extra tokens crossed eight times, which is
exactly the `24s` in the step count.  All the fixed pieces are the ones `FracP1.lean`
already proves; only the bookkeeping differs.
-/

namespace BB25

/-! ### The first two passes -/

/-- Shifting the window of a `3`-periodic run of `u` tokens by two cells. -/
lemma rep042_shift2 (k : ℕ) (t : List Sym) :
    (0 : Sym) :: 4 :: (rep [2, 0, 4] k ++ t) = rep [0, 4, 2] k ++ ((0 : Sym) :: 4 :: t) := by
  rw [rep_shift' 4 2 0 k, rep_shift' 0 4 2 k]

/-- **The first two passes**, in the presence of the extra run of `u`s. -/
theorem p1fs_pass12 (r s m : ℕ) :
    Win St.B St.B 3 (3 * r + 20)
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++ tokV 1 ++
        tokU 1 1 ++ rep (tokU 1 1) (s + 1) ++ tokU 1 (2 * m + 2) ++ [0])
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1] ++
        ([1] ++ rep [4, 2, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      (109 + 3 * r + 12 * s + 20 * m) := by
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring,
      replicate_split (2 : Sym) 2 (2 * m)]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      replicate_split (2 : Sym) 1 (2 * m)]; rfl
  have q4 : List.replicate (2 * m + 4) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 4 = 2 + (2 * m + 2) from by ring,
      replicate_split (2 : Sym) 2 (2 * m + 2)]; rfl
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  -- stage A : the opening
  have HA := p1g_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2] ++
      (rep [0, 4, 2] (s + 2) ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))))
  -- stage B : the carry crosses the run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3]
    ([4, 4, 2, 2, 4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage C : the `4`-run of `U(2,2)`
  have HC := (Win.of_sweepR hblk (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1))
    ([4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage D : the turn-around inside `U(2,2) V(1)`
  have HD := fp1_turn12.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0])
    ([4, 2] ++ (rep [0, 4, 2] (s + 1) ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage E : the run of `u`s after the `V`
  have HE := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 2)) (by simp) 0).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3])
    ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))
  -- stage F : the absorbing token
  have HF := (Win.of_sweepR sweepR_042 (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 2))
    (List.replicate (2 * m) 2 ++ [0])
  -- stage G : the round trip through the run of `2`s
  have HG := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) []
  -- stage H : the run of `u`s crossed leftwards
  have HH := (Win.of_sweepL (sweepL_bulk (s + 2)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 0, 1, 0])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage I : the `V` crossed leftwards
  have HI := (Win.of_sweepL (sweepL_bulk 1) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    (rep [2, 0, 4] (s + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage J : the second turn-around
  have HJ := fp1_turn2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    ([4] ++ (rep [2, 0, 4] (s + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage K : the second rightward pass
  have HK := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 3)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3])
    (List.replicate (2 * m + 2) 2 ++ [0])
  -- stage L : the ping-pong through the run of `2`s
  have HL := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1]) [0]
  -- stage M : the turn-around at the far end
  have HM := rule_endgame.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1] ++
      List.replicate (2 * m + 2) 1) []
  -- stage N : the return sweep over the run of `1`s
  have HN := (onesBack_gen 3 (2 * m + 6)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) []
  -- stage O : the marker is crossed
  have HO := (fp1_ret4_gen 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
      [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] s ++ [1])
    (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage P : the extra run of `u`s crossed leftwards in state `B`
  have HP := (Win.of_sweepL (sweepL_bulkB (s + 1)) 1).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1])
    ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++
        tokV 1 ++ tokU 1 1 ++ rep (tokU 1 1) (s + 1) ++ tokU 1 (2 * m + 2) ++
        [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2] ++
          (rep [0, 4, 2] (s + 2) ++ ([0, 4] ++
            (List.replicate (2 * m + 2) 2 ++ [0])))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV, rep_succ]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2, 2, 4, 3, 2] ++
          (rep [0, 4, 2] (s + 2) ++ ([0, 4] ++
            (List.replicate (2 * m + 2) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2, 2, 4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    rw [rep_succ (w := [0, 4, 2]) r]; simp
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2, 2, 4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([0, 4, 4, 2] ++ [2]) ++
        ([4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    simp
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([1, 0, 0, 3] ++ [2]) ++
        ([4, 3, 2] ++ (rep [0, 4, 2] (s + 2) ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        [0, 3, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] (s + 1) ++ ([0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    rw [rep_succ (w := [0, 4, 2]) (s + 1)]; simp
  have E4 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0]) ++
        [1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] (s + 1) ++ ([0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 2) ++ [0]) ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) := by
    rw [rep_succ (w := [0, 4, 2]) (s + 1)]; simp
  have E5 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 2) ++ [0]) ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 2)) ++ ([0, 4, 2] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q2]; simp
  have E6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 2)) ++ ([1, 0, 3] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [q1, rep_succ' (w := [1, 0, 3]) (s + 1)]; simp
  have E7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0]) ++ ((3 : Sym) :: rep [1, 0, 3] (s + 2)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [rep_succ' (w := [1, 0, 3]) (s + 1)]; simp
  have E8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 0, 1, 0]) ++ ((3 : Sym) :: rep [2, 0, 4] (s + 2)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ((0 : Sym) :: rep [1, 0, 3] 1) ++
        (rep [2, 0, 4] (s + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    simp [rep_succ]
  have E9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ((0 : Sym) :: rep [2, 0, 4] 1) ++
        (rep [2, 0, 4] (s + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [0, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] (s + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    simp [rep_succ]
  have E10 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ [1, 3, 0] ++
        ([4] ++ (rep [2, 0, 4] (s + 2) ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3]) ++ (rep [0, 4, 2] (s + 3) ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [q4, rep_succ' (w := [0, 4, 2]) (s + 2)]
    simp [rep042_shift2]
  have E11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3]) ++ (rep [1, 0, 3] (s + 3) ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1]) ++
        ([0, 3] ++ List.replicate (2 * (m + 1) + 1) 2) ++ [0] := by
    rw [show 2 * (m + 1) + 1 = 1 + (2 * m + 2) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 2), rep_succ' (w := [1, 0, 3]) (s + 2)]
    simp
  have E12 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1]) ++
        (List.replicate (2 * (m + 1)) 1 ++ [0, 3, 2]) ++ [0] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1] ++
          List.replicate (2 * m + 2) 1) ++ [0, 3, 2, 0] ++ [] := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring]; simp
  have E13 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 2) ++ [1] ++
          List.replicate (2 * m + 2) 1) ++ [1, 1, 1, 0] ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 1 ++ [0])) ++ [] := by
    have e : List.replicate (2 * m + 6) (1 : Sym)
        = 1 :: (List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) := by
      rw [show 2 * m + 6 = 1 + ((2 * m + 2) + 3) from by ring,
        replicate_split (1 : Sym) 1 ((2 * m + 2) + 3),
        replicate_split (1 : Sym) (2 * m + 2) 3]
      rfl
    rw [e, rep_succ' (w := [1, 0, 3]) (s + 1)]
    simp
  have E14 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] (s + 1) ++ [1, 0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 6) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] s ++ [1]) ++
        ((0 : Sym) :: [3, 1, 0, 3]) ++ (List.replicate (2 * m + 6) 2 ++ [0]) := by
    rw [rep_succ' (w := [1, 0, 3]) s]; simp
  have E15 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1, 1, 3] ++ rep [1, 0, 3] s ++ [1]) ++
        ((0 : Sym) :: [4, 2, 0, 4]) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ([1] ++ rep [3, 1, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    rw [rep_succ' (w := [3, 1, 0]) s]
    simp [rep_shift' 3 1 0 s]
  have E16 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 1, 1]) ++ ([1] ++ rep [4, 2, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1] ++ ([1] ++ rep [4, 2, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp
  -- chain the stages
  have SA : Win St.B St.A 3 13 _ _ 16 := HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 13 (3 * r + 16) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC : Win St.A St.A (3 * r + 16) (3 * r + 20) _ _ 4 :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 rfl
  have SD : Win St.A St.A (3 * r + 20) (3 * r + 24) _ _ 12 :=
    HD.cast (by simp; ring) (by simp; ring) rfl E4 rfl
  have SE : Win St.A St.A (3 * r + 24) (3 * r + 3 * s + 30) _ _ (3 * s + 6) :=
    HE.cast (by simp; ring) (by simp; ring) rfl E5 (by ring)
  have SF : Win St.A St.A (3 * r + 3 * s + 30) (3 * r + 3 * s + 33) _ _ 3 :=
    HF.cast (by simp; ring) (by simp; ring) rfl E6 rfl
  have SG : Win St.A St.A (3 * r + 3 * s + 33) (3 * r + 3 * s + 29) _ _ (10 * m + 14) :=
    HG.cast (by simp; ring) (by simp; ring) rfl E7 rfl
  have SH : Win St.A St.A (3 * r + 3 * s + 29) (3 * r + 23) _ _ (3 * s + 6) :=
    HH.cast (by simp; ring) (by simp; ring) rfl E8 (by ring)
  have SI : Win St.A St.A (3 * r + 23) (3 * r + 20) _ _ 3 :=
    HI.cast (by simp; ring) (by simp; ring) rfl E9 rfl
  have SJ : Win St.A St.A (3 * r + 20) (3 * r + 22) _ _ 2 :=
    HJ.cast (by simp; ring) (by simp; ring) rfl E10 rfl
  have SK : Win St.A St.A (3 * r + 22) (3 * r + 3 * s + 31) _ _ (3 * s + 9) :=
    HK.cast (by simp; ring) (by simp; ring) rfl E11 (by ring)
  have SL : Win St.A St.A (3 * r + 3 * s + 31) (3 * r + 3 * s + 2 * m + 33) _ _
      (8 * m + 8) :=
    HL.cast (by simp; ring) (by simp; ring) rfl E12 (by ring)
  have SM : Win St.A St.B (3 * r + 3 * s + 2 * m + 33) (3 * r + 3 * s + 2 * m + 34) _ _ 9 :=
    HM.cast (by simp; ring) (by simp; ring) rfl E13 rfl
  have SN : Win St.B St.A (3 * r + 3 * s + 2 * m + 34) (3 * r + 3 * s + 27) _ _
      (2 * m + 7) :=
    HN.cast (by simp; ring) (by simp; ring) rfl E14 (by ring)
  have SO : Win St.A St.B (3 * r + 3 * s + 27) (3 * r + 3 * s + 23) _ _ 4 :=
    HO.cast (by simp; ring) (by simp; ring) rfl E15 rfl
  have SP : Win St.B St.B (3 * r + 3 * s + 23) (3 * r + 20) _ _ (3 * s + 3) :=
    HP.cast (by simp; ring) (by simp; ring) rfl E16 (by ring)
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
  have T14 := T13.trans SO (by simp; omega)
  exact (T14.trans SP (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The third and fourth passes -/

/-- **The third and fourth passes**, in the presence of the extra run of `u`s.  The head
returns to the left end of the region, is reflected there, crosses the whole region twice
more and comes back to the marker, in exactly `130 + 6r + 12s + 20m` steps. -/
theorem p1fs_pass34 (r s m : ℕ) :
    Win St.B St.A (3 * r + 20) (3 * r + 20)
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 1, 1] ++
        ([1] ++ rep [4, 2, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])))
      (130 + 6 * r + 12 * s + 20 * m) := by
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
    (rep [4, 2, 0] (s + 1) ++
      ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
  -- stage Q : the run of `u`s crossed leftwards
  have HQ := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0]
    ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
      ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))
  -- stage R : into the run of `0`s
  have HR := fp1_two.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0]
    (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
      ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))))
  -- stage S : the reflection
  have HS := fp1_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    ([4] ++ (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
      ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))))
  -- stage T : the third rightward pass over the run of `u`s
  have HT := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 2)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1]
    ([0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
      ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))
  -- stage U : the swept `U(4,1)`
  have HU := fp1_crossU41.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2))
    (rep [4, 2, 0] s ++ ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
  -- stage V : the run of `u`s before the run of `2`s
  have HV := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 2)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0, 3])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage W : the third round trip through the run of `2`s
  have HW := cb2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1, 0]) []
  -- stage X : the run of `u`s crossed leftwards again
  have HX := (Win.of_sweepL (sweepL_bulk (s + 1)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0])
    (List.replicate (2 * m + 8) 2 ++ [0])
  -- stage Y : back into the run of `0`s
  have HY := fp1_two.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0])
    (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 8) 2 ++ [0]))
  -- stage Z : the second reflection
  have HZ := fp1_reflect.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0])
    ([4] ++ (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 8) 2 ++ [0])))
  -- stage AA : the fourth rightward pass over the run of `u`s
  have HAA := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (s + 2)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1])
    (List.replicate (2 * m + 7) 2 ++ [0])
  -- stage BB : one step into the run of `2`s
  have HBB := carry_B2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
      rep [3, 1, 0] (s + 2))
    (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage CC : the fourth round trip through the run of `2`s
  have HCC := cb3.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
      rep [3, 1, 0] (s + 1)) []
  -- stage DD : the last leftward crossing of the extra run of `u`s
  have HDD := (Win.of_sweepL (sweepL_bulk (s + 1)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1])
    (List.replicate (2 * m + 10) 2 ++ [0])
  -- the tape words the computation passes through
  have F0 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
        [1, 0, 1, 1] ++ ([1] ++ rep [4, 2, 0] (s + 1)) ++
        ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 1, 0, 1, 1, 1] ++
        (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) := by
    rw [rep_succ' (w := [1, 0, 3]) r]; simp
  have F1 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 2, 0, 4, 4, 4] ++
        (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [1, 0, 3] (r + 1)) ++
        ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) := by
    rw [rep_succ' (w := [1, 0, 3]) r]; simp
  have F2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [2, 0, 4] (r + 1)) ++
        ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0] ++ [0, 0, 3] ++
        (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))) := by
    simp
  have F3 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0] ++ [0, 0, 4] ++
        (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0] ++
        ([4] ++ (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))))) := by
    simp
  have F4 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] (r + 1) ++ ([2, 0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ (rep [2, 0, 4] (r + 2) ++ [2]) ++
        ([0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) := by
    simp [rep_succ]
  have F5 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ (rep [3, 1, 0] (r + 2) ++ [2]) ++
        ([0, 4, 4, 4] ++ (rep [4, 2, 0] (s + 1) ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2)) ++
        [2, 0, 4, 4, 4, 4, 2, 0] ++
        (rep [4, 2, 0] s ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) := by
    rw [rep_succ (w := [4, 2, 0]) s]; simp
  have F6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2)) ++
        [3, 1, 0, 0, 0, 0, 3, 0] ++
        (rep [4, 2, 0] s ++
          ([4, 2, 0, 4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3]) ++ (rep [0, 4, 2] (s + 2) ++ [2]) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [p6, rep_succ' (w := [0, 4, 2]) (s + 1), rep_succ' (w := [0, 4, 2]) s]
    simp [rep_shift' 0 4 2 s]
  have F7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3]) ++ (rep [1, 0, 3] (s + 2) ++ [2]) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] s ++ [1, 0]) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 5) 2 ++ [0])) ++ [] := by
    rw [p5, rep_succ' (w := [1, 0, 3]) (s + 1), rep_succ' (w := [1, 0, 3]) s]; simp
  have F8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] s ++ [1, 0]) ++
        ((3 : Sym) :: (List.replicate (2 * m + 8) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0, 0, 0]) ++
        ((3 : Sym) :: rep [1, 0, 3] (s + 1)) ++
        (List.replicate (2 * m + 8) 2 ++ [0]) := by
    rw [rep_succ' (w := [1, 0, 3]) s]; simp
  have F9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++
          [3, 1, 0, 0, 0, 0]) ++ ((3 : Sym) :: rep [2, 0, 4] (s + 1)) ++
        (List.replicate (2 * m + 8) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0]) ++
        [0, 0, 3] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 8) 2 ++ [0])) := by
    simp
  have F10 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 0]) ++
        [0, 0, 4] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 8) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0]) ++
        [0, 0, 0] ++
        ([4] ++ (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 8) 2 ++ [0]))) := by
    simp
  have F11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0]) ++
        [1, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 8) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        (rep [2, 0, 4] (s + 2) ++ [2]) ++ (List.replicate (2 * m + 7) 2 ++ [0]) := by
    rw [p8]; simp [rep_succ]
  have F12 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        (rep [3, 1, 0] (s + 2) ++ [2]) ++
        (List.replicate (2 * m + 7) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
          rep [3, 1, 0] (s + 2)) ++ [2, 2] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    rw [p7]; simp
  have F13 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
          rep [3, 1, 0] (s + 2)) ++ [3, 2] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
          rep [3, 1, 0] (s + 1)) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 7) 2 ++ [0])) ++ [] := by
    rw [p7, rep_succ' (w := [3, 1, 0]) (s + 1)]; simp
  have F14 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1] ++
          rep [3, 1, 0] (s + 1)) ++
        ((3 : Sym) :: (List.replicate (2 * m + 10) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ((3 : Sym) :: rep [1, 0, 3] (s + 1)) ++
        (List.replicate (2 * m + 10) 2 ++ [0]) := by
    simp [rep_shift' 3 1 0 (s + 1)]
  have F15 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1]) ++
        ((3 : Sym) :: rep [2, 0, 4] (s + 1)) ++
        (List.replicate (2 * m + 10) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])) := by
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
  have SV : Win St.A St.A (3 * r + 23) (3 * r + 3 * s + 29) _ _ (3 * s + 6) :=
    HV.cast (by simp; ring) (by simp; ring) rfl F7 (by ring)
  have SW : Win St.A St.A (3 * r + 3 * s + 29) (3 * r + 3 * s + 25) _ _ (10 * m + 34) :=
    HW.cast (by simp; ring) (by simp; ring) rfl F8 rfl
  have SX : Win St.A St.A (3 * r + 3 * s + 25) (3 * r + 22) _ _ (3 * s + 3) :=
    HX.cast (by simp; ring) (by simp; ring) rfl F9 (by ring)
  have SY : Win St.A St.A (3 * r + 22) (3 * r + 20) _ _ 2 :=
    HY.cast (by simp; ring) (by simp; ring) rfl F10 rfl
  have SZ : Win St.A St.B (3 * r + 20) (3 * r + 20) _ _ 4 :=
    HZ.cast (by simp; ring) (by simp; ring) rfl F11 rfl
  have SAA : Win St.B St.B (3 * r + 20) (3 * r + 3 * s + 26) _ _ (3 * s + 6) :=
    HAA.cast (by simp; ring) (by simp; ring) rfl F12 (by ring)
  have SBB : Win St.B St.A (3 * r + 3 * s + 26) (3 * r + 3 * s + 27) _ _ 1 :=
    HBB.cast (by simp; ring) (by simp; ring) rfl F13 rfl
  have SCC : Win St.A St.A (3 * r + 3 * s + 27) (3 * r + 3 * s + 23) _ _ (10 * m + 44) :=
    HCC.cast (by simp; ring) (by simp; ring) rfl F14 rfl
  have SDD : Win St.A St.A (3 * r + 3 * s + 23) (3 * r + 20) _ _ (3 * s + 3) :=
    HDD.cast (by simp; ring) (by simp; ring) rfl F15 (by ring)
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
  have U12 := U11.trans SBB (by simp; omega)
  have U13 := U12.trans SCC (by simp; omega)
  exact (U13.trans SDD (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The return to the left end -/

/-- **The return to the left end**, in the presence of the extra run of `u`s.  The head
crosses the region leftwards one last time, rebuilds the prefix `U(2,2) u U(2,1)` and
stops, in state `B`, on the new leftmost non-blank cell, in exactly `22 + 3r` steps.  The
extra run of `u`s lies to the right of everything this pass touches, so the step count is
the same as without it. -/
theorem p1fs_return (r s m : ℕ) :
    Win St.A St.B (3 * r + 20) 0
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])))
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 10) ++ [0])
      (22 + 3 * r) := by
  -- stage EE : the run of `2`s is left behind
  have HEE := fp1_backL.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1])
    (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0]))
  -- stage FF : the run of `u`s crossed leftwards in state `B`
  have HFF := (Win.of_sweepL (sweepL_bulkB (r + 1)) 1).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0]
    ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
      (List.replicate (2 * m + 10) 2 ++ [0])))
  -- stage GG : one step
  have HGG := fp1_B1.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1]
    (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
        (List.replicate (2 * m + 10) 2 ++ [0]))))
  -- stage HH : the last block
  have HHH := fp1_pre.embed (by simp) [0, 1, 3, 1]
    ([4] ++ (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
        (List.replicate (2 * m + 10) 2 ++ [0])))))
  -- stage II : the closing
  have HII := fp1_close.embed (by simp) []
    ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
      ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
        (List.replicate (2 * m + 10) 2 ++ [0])))))
  -- the tape words the computation passes through
  have G0 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] (r + 2) ++ [3, 1, 0, 1, 3] ++
        (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 10) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [0, 3, 1, 0, 3, 1, 0, 1, 3] ++
        (rep [2, 0, 4] (s + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])) := by
    rw [show r + 2 = r + 1 + 1 from rfl, rep_succ' (w := [3, 1, 0]) (r + 1),
      rep_succ' (w := [3, 1, 0]) r]
    simp
  have G1 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [0, 4, 2, 0, 4, 2, 0, 4, 4] ++
        (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 10) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ ((1 : Sym) :: rep [3, 1, 0] (r + 1)) ++
        ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 10) 2 ++ [0]))) := by
    rw [rep_succ' (w := [3, 1, 0]) r]; simp
  have G2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ ((1 : Sym) :: rep [4, 2, 0] (r + 1)) ++
        ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
          (List.replicate (2 * m + 10) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 1] ++
        (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0])))) := by
    simp
  have G3 : ([0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 4] ++
        (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1] ++ [0, 0, 3, 1, 0] ++
        ([4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0]))))) := by
    simp
  have G4 : ([0, 1, 3, 1] ++ [0, 0, 4, 2, 0] ++
        ([4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0]))))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0] ++
        ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0]))))) := by
    simp
  have G5 : ([] ++ [0, 4, 4, 2, 2, 0] ++
        ([4, 2, 0, 4] ++ (rep [4, 2, 0] (r + 1) ++
          ([4, 2, 0, 4, 2, 0, 4, 4] ++ (rep [2, 0, 4] (s + 1) ++
            (List.replicate (2 * m + 10) 2 ++ [0]))))) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 10) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl,
      show r + 2 = r + 1 + 1 from rfl, rep_succ' (w := [0, 4, 2]) (r + 1)]
    simp [tokU, rep_shift', rep_succ']
  -- chain the stages
  have SEE : Win St.A St.B (3 * r + 20) (3 * r + 12) _ _ 8 :=
    HEE.cast (by simp; ring) (by simp; ring) G0.symm G1 rfl
  have SFF : Win St.B St.B (3 * r + 12) 9 _ _ (3 * r + 3) :=
    HFF.cast (by simp; ring) (by simp) rfl G2 (by ring)
  have SGG : Win St.B St.B 9 8 _ _ 1 := HGG.cast (by simp) (by simp) rfl G3 rfl
  have SHH : Win St.B St.A 8 4 _ _ 4 := HHH.cast (by simp) (by simp) rfl G4 rfl
  have SII : Win St.A St.B 4 0 _ _ 6 := HII.cast (by simp) (by simp) rfl G5 rfl
  have V1 := SEE.trans SFF (by simp; omega)
  have V2 := V1.trans SGG (by simp; omega)
  have V3 := V2.trans SHH (by simp; omega)
  exact (V3.trans SII (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### The rule -/

/-- **The `P1` macro rule of the fractal row, with intervening tokens.**  For all
`r, s, m`, from the window

`0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · u^(s+1) · U(1,2m+2) 0`

the machine reaches, in exactly `261 + 12r + 24s + 40m` steps, the window

`U(2,2) u · U(2,1) · u^(r+2) · U(2,1) · u^s · U(1,2m+10) 0`,

again in state `B` on the new leftmost non-blank cell, three cells further left.  This is
the variant of `rule_P1_fractal` in which at least one token `u` separates the inner
`U(2,2) V(1) u` from the token that absorbs the carry; the head makes four passes, and the
extra run of `u`s is crossed eight times, which is the `24s` in the step count. -/
theorem rule_P1_fractal_gen (r s m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 2 ++ tokV 1 ++
        tokU 1 1 ++ rep (tokU 1 1) (s + 1) ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (r + 2) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 10) ++ [0])
      (261 + 12 * r + 24 * s + 40 * m) := by
  have h1 := (p1fs_pass12 r s m).trans (p1fs_pass34 r s m) (by simp; omega)
  have h2 := h1.trans (p1fs_return r s m) (by simp; omega)
  exact h2.cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P1_fractal_gen` is being applied. -/
theorem rule_P1_fractal_gen_no_halt (r s m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ rep (tokU 1 1) (s + 1) ++ tokU 1 (2 * m + 2) ++
      [0])) :
    ∀ i ≤ 261 + 12 * r + 24 * s + 40 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1_fractal_gen r s m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
