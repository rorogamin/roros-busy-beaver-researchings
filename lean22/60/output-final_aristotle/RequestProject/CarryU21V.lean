import RequestProject.CarryU21bV

/-!
# A crossed `U(2,1)`, an absorbing `U(1,even)` and a `V` after it

This is the last of the two census rows of `ANALYSIS.md` §31 in which one of the crossed
tokens has exponent `a = 2` and a token `V` follows the token that absorbs the carry;
`CarryU21bV.lean` proved the one in which the absorbing token is a `U(2,b)`, and this file
proves the one in which it is a `U(1,b)`:

```
0 0 0 · U(2,2) V(1) · u^(r+1) · U(2,1) · u^s · U(1,2m+2) · V(2c+5) · u^w · U(1,2m'+2) 0
       --(137 + 12r + 6s + 10m + 10c + 6w + 10m') steps-->
   U(2,1) U(4,1) · u^r · U(1,4) · u^s · U(1,2m+4) · V(2c+3) · u^w · U(1,2m'+4) 0
```

It combines the two mechanisms that the earlier files isolated.  The crossed token `U(2,1)`
swallows two of the four `2`s of the carry and becomes `U(1,4)` (`u21_turn`, as in
`rule_P3_U21`), so only a carry of **two** travels on; and the `V` does not stop that
carry (`vcross_step`, as in `rule_P3_V`), so the two `2`s are shared out as `+2` for the
absorbing token, `-2` for the `V` and `+2` for the token after it.  As in `rule_P3_V` the
rule is stated for `V(2c+5)`: the short `V`s in this position make the machine halt.

The computation is exhibited as twenty-three macro steps, all of them pieces that the
earlier files already provide.  Because the second pass is turned around by the crossed
`U(2,1)`, the head crosses the run `u^r` four times but everything to the right of the
`U(2,1)` only twice.
-/

namespace BB25

set_option maxHeartbeats 2000000 in
/-- **The `P3` rule with a crossed `U(2,1)`, an absorbing `U(1,2m+2)` and a `V(2c+5)`.**
The head is in state `B` on the leftmost non-blank cell, with three blank cells to its
left, and the tape reads

`U(2,2) V(1) · u^(r+1) · U(2,1) · u^s · U(1,2m+2) · V(2c+5) · u^w · U(1,2m'+2)`

followed by the `0` of the next token.  In exactly
`137 + 12r + 6s + 10m + 10c + 6w + 10m'` steps the crossed token becomes `U(1,4)`, the
absorbing token becomes `U(1,2m+4)`, the `V` gives up two `2`s and the token after it
gains two, and the head arrives, again in state `B`, on the new leftmost non-blank cell
three cells further left.  Nothing outside the window is read or written. -/
theorem rule_P3_U21_V (r s m c w mp : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ tokV (2 * c + 5) ++ rep (tokU 1 1) w ++
        tokU 1 (2 * mp + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ rep (tokU 1 1) s ++
        tokU 1 (2 * m + 4) ++ tokV (2 * c + 3) ++ rep (tokU 1 1) w ++
        tokU 1 (2 * mp + 4) ++ [0])
      (137 + 12 * r + 6 * s + 10 * m + 10 * c + 6 * w + 10 * mp) := by
  -- splitting the runs
  have hz2m2 : List.replicate (2 * m + 2) (2 : Sym) = [2] ++ List.replicate (2 * m + 1) 2 := by
    rw [show 2 * m + 2 = 1 + (2 * m + 1) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 1)]
    rfl
  have hz2m1 : List.replicate (2 * m + 1) (2 : Sym) = [2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split (2 : Sym) 1 (2 * m)]
    rfl
  have hz2c5 : List.replicate (2 * c + 5) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * c + 3) 2 := by
    rw [show 2 * c + 5 = 2 + (2 * c + 3) from by ring,
      replicate_split (2 : Sym) 2 (2 * c + 3)]
    rfl
  have ho2c5 : List.replicate (2 * c + 5) (1 : Sym)
      = List.replicate (2 * c + 2) 1 ++ [1, 1, 1] := by
    rw [show 2 * c + 5 = (2 * c + 2) + 3 from by ring,
      replicate_split (1 : Sym) (2 * c + 2) 3]
    rfl
  have hz2mp2 : List.replicate (2 * mp + 2) (2 : Sym)
      = [2] ++ List.replicate (2 * mp + 1) 2 := by
    rw [show 2 * mp + 2 = 1 + (2 * mp + 1) from by ring,
      replicate_split (2 : Sym) 1 (2 * mp + 1)]
    rfl
  have hz2mp1 : List.replicate (2 * mp + 1) (2 : Sym) = [2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 1 = 1 + 2 * mp from by ring, replicate_split (2 : Sym) 1 (2 * mp)]
    rfl
  -- the block `U(2,1)` crossed rightwards, followed by the run of `u`s
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  have hCD : SweepR St.A St.A
      ([0, 4, 4, 2] ++ rep [0, 4, 2] (s + 1)) ([1, 0, 0, 3] ++ rep [1, 0, 3] (s + 1))
      (4 + (s + 1) * 3) :=
    hblk.comp (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp)
  -- the twenty-three stages
  have H1 := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++
        (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))))))
  have H2 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++ (List.replicate (2 * m + 1) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
        ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))))
  have H3 := (Win.of_sweepR hCD (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1))
    (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  have H4 := (pingpong_chain0 m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1])
    ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
      ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))
  have H5 := vcross_step.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1)
    (List.replicate (2 * c + 3) 2 ++ (rep [0, 4, 2] w ++
      ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have H6 := (pingpong_chain0 (c + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1])
    ([2] ++ (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have H7 := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
      List.replicate (2 * c + 2) 1)
    (rep [4, 2, 0] w ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))
  have H8 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (w + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
      List.replicate (2 * c + 2) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp) 2 ++ [0])
  have H9 := (cross_back mp).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
      List.replicate (2 * c + 2) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] w) []
  have H10 := (Win.of_sweepL (sweepL_bulk w) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
      List.replicate (2 * c + 2) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 4) 2 ++ [0])
  have H11 := (Win.of_sweepL retV 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
      List.replicate (2 * c + 2) 1 ++ [1])
    (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
  have H12 := (Win.of_sweepL (run_ones_A (2 * c + 5)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1])
    ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have H13 := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1])
    (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have H14 := (Win.of_sweepL (run_ones_A (2 * m + 1)) 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
      rep [1, 0, 3] s ++ [1, 1])
    ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
  have H15 := (Win.of_sweepL (run_ones_A 3) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
      rep [3, 1, 0] s)
    (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have H16 := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0])
    ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
      (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
        (List.replicate (2 * mp + 4) 2 ++ [0])))))))
  have H17 := (Win.of_sweepL blockL_1003 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
      (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
        (List.replicate (2 * mp + 4) 2 ++ [0]))))))))
  have H18 := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
        (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
  have H19 := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
      (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))))))))
  have H20 := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
        (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
  have H21 := u21_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r)
    (4 :: (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
      ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
        (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
  have H22 := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
      (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
  have H23 := p3_final.embed (by simp) []
    (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
      (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ tokV (2 * c + 5) ++ rep (tokU 1 1) w ++
        tokU 1 (2 * mp + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++
            (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
              ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++
            (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
              ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))) := by
    rw [rep_succ ([0, 4, 2] : List Sym) r, rep_succ' ([0, 4, 2] : List Sym) s, hz2m2]
    simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([0, 4, 4, 2] ++ rep [0, 4, 2] (s + 1)) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    rw [hz2m1]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([1, 0, 0, 3] ++ rep [1, 0, 3] (s + 1)) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1]) ++ ([0, 3] ++ List.replicate (2 * m + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) s, hz2m1]; simp
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1]) ++ (List.replicate (2 * m) 1 ++ [0, 3, 2]) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++ (rep [0, 4, 2] w ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1) ++ [0, 3, 2, 4, 3, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++ (rep [0, 4, 2] w ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1) ++ [1, 1, 0, 1, 0, 3, 2] ++
        (List.replicate (2 * c + 3) 2 ++ (rep [0, 4, 2] w ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * c + 3) 2) ++
        ([2] ++ (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    simp [replicate_cons_comm]
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        (List.replicate (2 * c + 2) 1 ++ [0, 3, 2]) ++
        ([2] ++ (rep [0, 4, 2] w ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1) ++ [0, 3, 2, 2, 0] ++
        (rep [4, 2, 0] w ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    have key : ∀ X : List Sym,
        rep [0, 4, 2] w ++ ((0 : Sym) :: 4 :: X) = 0 :: (rep [4, 2, 0] w ++ (4 :: X)) :=
      fun X => (rep_shift' (0 : Sym) 4 2 w (4 :: X)).symm
    simp [key]
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1) ++ [1, 1, 0, 3, 0] ++
        (rep [4, 2, 0] w ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0, 3]) ++
        (rep [0, 4, 2] (w + 1) ++ [2]) ++ (List.replicate (2 * mp) 2 ++ [0]) := by
    rw [rep_succ' ([0, 4, 2] : List Sym) w, hz2mp2, hz2mp1, ← rep_shift' (0 : Sym) 4 2 w]
    simp
  have E8 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0, 3]) ++
        (rep [1, 0, 3] (w + 1) ++ [2]) ++ (List.replicate (2 * mp) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] w) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * mp + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ' ([1, 0, 3] : List Sym) w, hz2mp1]
    simp [rep_shift']
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] w) ++
        (3 :: (List.replicate (2 * mp + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0]) ++ (3 :: rep [1, 0, 3] w) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) := by
    simp [rep_shift']
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1, 1, 0]) ++ (3 :: rep [2, 0, 4] w) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1]) ++ [1, 0, 3] ++
        (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])) := by
    simp
  have E11 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++
          List.replicate (2 * c + 2) 1 ++ [1]) ++ [1, 0, 4] ++
        (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1]) ++
        ([0] ++ List.replicate (2 * c + 5) 1) ++
        ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    rw [ho2c5]; simp [replicate_cons_comm]
  have E12 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1]) ++
        ([0] ++ List.replicate (2 * c + 5) 2) ++
        ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1]) ++ [0, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E13 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1] ++ List.replicate (2 * m) 1 ++ [1, 1]) ++ [1, 4, 3] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1, 1]) ++ ([1] ++ List.replicate (2 * m + 1) 1) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split (1 : Sym) 1 (2 * m)]
    simp [replicate_cons_comm]
  have E14 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] s ++ [1, 1]) ++ ([1] ++ List.replicate (2 * m + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          rep [3, 1, 0] s) ++ [3, 1, 1, 1] ++
        (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    simp [rep_shift']
  have E15 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          rep [3, 1, 0] s) ++ [3, 2, 2, 2] ++
        (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: rep [1, 0, 3] s) ++
        ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0]))))))) := by
    simp [rep_shift']
  have E16 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: rep [2, 0, 4] s) ++
        ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))) : List Sym))
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 1, 0, 0, 3] ++
        (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) r]; simp
  have E17 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        [3, 2, 2, 0, 4] ++
        (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))))) := by
    rw [rep_succ' ([1, 0, 3] : List Sym) r]; simp
  have E18 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++
              (List.replicate (2 * mp + 4) 2 ++ [0]))))))))))) := by
    rw [rep_succ ([2, 0, 4] : List Sym) r]; simp
  have E19 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0]))))))))) := by
    rw [rep_succ ([2, 0, 4] : List Sym) r]; simp
  have E20 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))))) : List Sym))
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++ [3, 1, 0, 2, 2, 0] ++
        (4 :: (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0]))))))))) := by
    rw [rep_succ' ([3, 1, 0] : List Sym) r]; simp
  have E21 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        [3, 2, 2, 2, 2, 0] ++
        (4 :: (rep [2, 0, 4] s ++ ([2, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++
          ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++ ([0, 4] ++ (rep [2, 0, 4] w ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))))) : List Sym))
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))))) := by
    simp [rep_shift']
  have E22 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))))))
        : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++
              (List.replicate (2 * mp + 4) 2 ++ [0])))))))))) := by
    simp
  have E23 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ ([2, 2, 2] ++
          (List.replicate (2 * m + 1) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] w ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))))))
        : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ rep (tokU 1 1) s ++
        tokU 1 (2 * m + 4) ++ tokV (2 * c + 3) ++ rep (tokU 1 1) w ++
        tokU 1 (2 * mp + 4) ++ [0] := by
    have e4 : List.replicate (2 * m + 4) (2 : Sym)
        = [2, 2, 2] ++ List.replicate (2 * m + 1) 2 := by
      rw [show 2 * m + 4 = 3 + (2 * m + 1) from by ring,
        replicate_split (2 : Sym) 3 (2 * m + 1)]
      rfl
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp only [tokU, tokV, e4]
    simp [rep_shift']
  -- chain the stages
  have S1 : Win St.B St.A 3 11 _ _ 22 :=
    H1.cast (by simp) (by simp) E0.symm E1 rfl
  have S2 : Win St.A St.A 11 (3 * r + 14) _ _ (3 * r + 3) :=
    H2.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have S3 : Win St.A St.A (3 * r + 14) (3 * r + 3 * s + 21) _ _ (3 * s + 7) :=
    H3.cast (by simp; omega) (by simp; omega) rfl E3 (by ring)
  have S4 : Win St.A St.A (3 * r + 3 * s + 21) (3 * r + 3 * s + 2 * m + 21) _ _ (8 * m) :=
    H4.cast (by simp; omega) (by simp; omega) rfl E4 rfl
  have S5 : Win St.A St.A (3 * r + 3 * s + 2 * m + 21) (3 * r + 3 * s + 2 * m + 25) _ _ 12 :=
    H5.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have S6 : Win St.A St.A (3 * r + 3 * s + 2 * m + 25)
      (3 * r + 3 * s + 2 * m + 2 * c + 27) _ _ (8 * c + 8) :=
    H6.cast (by simp; omega) (by simp; omega) rfl E6 (by ring)
  have S7 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 27)
      (3 * r + 3 * s + 2 * m + 2 * c + 29) _ _ 8 :=
    H7.cast (by simp; omega) (by simp; omega) rfl E7 rfl
  have S8 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 29)
      (3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 32) _ _ (3 * w + 3) :=
    H8.cast (by simp; omega) (by simp; omega) rfl E8 (by ring)
  have S9 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 32)
      (3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 28) _ _ (10 * mp + 14) :=
    H9.cast (by simp; omega) (by simp; omega) rfl E9 rfl
  have S10 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 3 * w + 28)
      (3 * r + 3 * s + 2 * m + 2 * c + 28) _ _ (3 * w) :=
    H10.cast (by simp; omega) (by simp; omega) rfl E10 (by ring)
  have S11 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 28)
      (3 * r + 3 * s + 2 * m + 2 * c + 26) _ _ 2 :=
    H11.cast (by simp; omega) (by simp; omega) rfl E11 rfl
  have S12 : Win St.A St.A (3 * r + 3 * s + 2 * m + 2 * c + 26)
      (3 * r + 3 * s + 2 * m + 21) _ _ (2 * c + 5) :=
    H12.cast (by simp; omega) (by simp; omega) rfl E12 rfl
  have S13 : Win St.A St.A (3 * r + 3 * s + 2 * m + 21) (3 * r + 3 * s + 2 * m + 21) _ _ 4 :=
    H13.cast (by simp; omega) (by simp; omega) rfl E13 rfl
  have S14 : Win St.A St.A (3 * r + 3 * s + 2 * m + 21) (3 * r + 3 * s + 20) _ _
      (2 * m + 1) :=
    H14.cast (by simp; omega) (by simp; omega) rfl E14 rfl
  have S15 : Win St.A St.A (3 * r + 3 * s + 20) (3 * r + 3 * s + 17) _ _ 3 :=
    H15.cast (by simp; omega) (by simp; omega) rfl E15 rfl
  have S16 : Win St.A St.A (3 * r + 3 * s + 17) (3 * r + 17) _ _ (3 * s) :=
    H16.cast (by simp; omega) (by simp; omega) rfl E16 (by ring)
  have S17 : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ 6 :=
    H17.cast (by simp; omega) (by simp; omega) rfl E17 rfl
  have S18 : Win St.A St.A (3 * r + 13) 10 _ _ (3 * r + 3) :=
    H18.cast (by simp; omega) (by simp) rfl E18 (by ring)
  have S19 : Win St.A St.B 10 11 _ _ 7 :=
    H19.cast (by simp) (by simp) rfl E19 rfl
  have S20 : Win St.B St.B 11 (3 * r + 14) _ _ (3 * r + 3) :=
    H20.cast (by simp) (by simp; ring) rfl E20 (by ring)
  have S21 : Win St.B St.A (3 * r + 14) (3 * r + 11) _ _ 15 :=
    H21.cast (by simp; omega) (by simp; omega) rfl E21 rfl
  have S22 : Win St.A St.A (3 * r + 11) 11 _ _ (3 * r) :=
    H22.cast (by simp; omega) (by simp) rfl E22 (by ring)
  have S23 : Win St.A St.B 11 0 _ _ 11 :=
    H23.cast (by simp) (by simp) rfl E23 rfl
  have T1 := S1.trans S2 (by simp; omega)
  have T2 := T1.trans S3 (by simp; omega)
  have T3 := T2.trans S4 (by simp; omega)
  have T4 := T3.trans S5 (by simp; omega)
  have T5 := T4.trans S6 (by simp; omega)
  have T6 := T5.trans S7 (by simp; omega)
  have T7 := T6.trans S8 (by simp; omega)
  have T8 := T7.trans S9 (by simp; omega)
  have T9 := T8.trans S10 (by simp; omega)
  have T10 := T9.trans S11 (by simp; omega)
  have T11 := T10.trans S12 (by simp; omega)
  have T12 := T11.trans S13 (by simp; omega)
  have T13 := T12.trans S14 (by simp; omega)
  have T14 := T13.trans S15 (by simp; omega)
  have T15 := T14.trans S16 (by simp; omega)
  have T16 := T15.trans S17 (by simp; omega)
  have T17 := T16.trans S18 (by simp; omega)
  have T18 := T17.trans S19 (by simp; omega)
  have T19 := T18.trans S20 (by simp; omega)
  have T20 := T19.trans S21 (by simp; omega)
  have T21 := T20.trans S22 (by simp; omega)
  exact (T21.trans S23 (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U21_V` is being applied. -/
theorem rule_P3_U21_V_no_halt (r s m c w mp : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
      rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ tokV (2 * c + 5) ++ rep (tokU 1 1) w ++
      tokU 1 (2 * mp + 2) ++ [0])) :
    ∀ i ≤ 137 + 12 * r + 6 * s + 10 * m + 10 * c + 6 * w + 10 * mp,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U21_V r s m c w mp).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
