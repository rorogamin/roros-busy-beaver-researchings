import RequestProject.CarryU21b

/-!
# A crossed `U(2,1)`, an absorbing `U(2,b)` and a `V` after it

`CarryU21b.lean` proved the rule in which the token that absorbs the carry is a `U(2,b)`
and one of the crossed tokens has exponent `a = 2`; there the window stopped at the `0`
that begins the next token.  This file proves the companion rule in which that next token
is a `V(1)` instead.  The carry is then *not* stopped at the absorbing token: it is handed
across the `V`, the tokens to the right of it are visited twice more, and the absorbing
token ends up as a long run of `4`s — a "virtual blank tape" in the sense of §24 of
`ANALYSIS.md`.

```
0 0 0 · U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) V(1) · u^(t+1) · U(1,2m'+2) 0
       --(167 + 6r + 10m + 12t + 20m') steps-->
   U(2,1) U(4,1) · U(1,4) · u^(r+1) · U(2m+6,1) · u^t · U(1,2m'+6) 0
```

Two new pieces are needed.  `vcross_end` is `vcross_step` for a token `V(1)`: the cell the
head stops on is the `0` that begins the next token rather than another `2`.  `sweepR_02`
is the two-step rightward crossing of the pair `0 2` that a `V(1)` leaves behind after the
first pass.  Everything else — `carry_open`, `blockR 2`, `pingpong_chain0`, `cross_back`,
`sweepL_bulk`, `run_ones_A`, `run_ones_B`, `sweepL_310`, `p3_final` — is already proved.
The computation is exhibited as twenty-six macro steps.
-/

namespace BB25

/-! ### The two new pieces -/

/-- **The ping-pong marker walks through a `V(1)`.**  This is `vcross_step` in the case in
which the token `V` has a single `2`, so that the cell the head stops on is the `0` that
begins the next token; that cell is only read. -/
theorem vcross_end : Win St.A St.A 2 6 [0, 3, 2, 4, 3, 2, 0] [1, 1, 0, 1, 0, 3, 0] 12 :=
  Win.of_lrun (by decide)

/-- **The pair `0 2` is crossed rightwards in two steps.**  This is what is left of a
token `V(1)` after the first pass has walked through it. -/
theorem sweepR_02 : SweepR St.A St.A [0, 2] [1, 3] 2 := by
  have h := sweepR_A0.comp sweepR_B2 (by simp)
  norm_num at h
  exact h

/-- The leftward pass in state `B` over a run of blocks `3 1 0`. -/
theorem sweepL_bulkB (k : ℕ) :
    SweepL St.B St.B (rep [3, 1, 0] k) (rep [4, 2, 0] k) (k * 3) :=
  sweepL_rep sweepL_310 (by simp) k

/-! ### The rule -/

set_option maxHeartbeats 2000000 in
/-- **The `P3` rule with a crossed `U(2,1)`, an absorbing `U(2,2m+4)` and a `V(1)` after
it.**  The head is in state `B` on the leftmost non-blank cell, with three blank cells to
its left, and the tape reads

`U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) V(1) · u^(t+1) · U(1,2m'+2)`

followed by the `0` of the next token.  In exactly `167 + 6r + 10m + 12t + 20m'` steps the
absorbing token and the `V(1)` after it become the single token `U(2m+6,1)`, the crossed
`U(2,1)` becomes `U(1,4)`, one more `u` appears in front of it, the last token becomes
`U(1,2m'+6)`, and the head arrives, again in state `B`, on the new leftmost non-blank cell
three cells further left.  Nothing outside the window is read or written. -/
theorem rule_P3_U21_U2b_V (r m t mp : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
        tokU 2 (2 * m + 4) ++ tokV 1 ++ rep (tokU 1 1) (t + 1) ++ tokU 1 (2 * mp + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) (r + 1) ++ tokU (2 * m + 6) 1 ++
        rep (tokU 1 1) t ++ tokU 1 (2 * mp + 6) ++ [0])
      (167 + 6 * r + 10 * m + 12 * t + 20 * mp) := by
  -- splitting the runs
  have hZ : List.replicate (2 * m + 4) (2 : Sym) = [2, 2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 4 = 2 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hY2 : List.replicate (2 * mp + 2) (2 : Sym)
      = [2] ++ List.replicate (2 * mp + 1) 2 := by
    rw [show 2 * mp + 2 = 1 + (2 * mp + 1) from by ring, replicate_split]; rfl
  have hY1 : List.replicate (2 * mp + 1) (2 : Sym) = [2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 1 = 1 + 2 * mp from by ring, replicate_split]; rfl
  have hY4 : List.replicate (2 * mp + 4) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * mp + 2) 2 := by
    rw [show 2 * mp + 4 = 2 + (2 * mp + 2) from by ring, replicate_split]; rfl
  have hone : List.replicate (2 * m + 5) (1 : Sym)
      = List.replicate (2 * m + 2) 1 ++ [1, 1, 1] := by
    rw [show 2 * m + 5 = (2 * m + 2) + 3 from by ring, replicate_split]; rfl
  have hfour : List.replicate (2 * m + 6) (4 : Sym)
      = List.replicate (2 * m + 5) 4 ++ [4] := by
    rw [show 2 * m + 6 = (2 * m + 5) + 1 from by ring, replicate_split]; rfl
  -- the block `U(2,·)` crossed rightwards
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  -- abbreviations for the two tails
  -- the twenty-six stages
  have H1 := carry_open.embed (by simp) []
    ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
      (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
        ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))))
  have H2 := (Win.of_sweepR sweepR_042 (by simp) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
      (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
        ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))))
  have H3 := (Win.of_sweepR hblk (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3])
    (rep [4, 2, 0] r ++ ([4, 4] ++
      (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
        ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))
  have H4 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) r) (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3])
    ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
      ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  have H5 := (Win.of_sweepR hblk (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r)
    (List.replicate (2 * m + 2) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
      ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))
  have H6 := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0])
    ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
      ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have H7 := vcross_end.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1)
    ([4, 2] ++ (rep [0, 4, 2] t ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have H8 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (t + 2)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0, 3])
    (List.replicate (2 * mp) 2 ++ [0])
  have H9 := (cross_back mp).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0] ++ rep [3, 1, 0] (t + 1)) []
  have H10 := (Win.of_sweepL (sweepL_bulk (t + 2)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1])
    (List.replicate (2 * mp + 4) 2 ++ [0])
  have H11 := (Win.of_sweepR sweepR_02 (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1])
    ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have H12 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (t + 2)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1, 3])
    (List.replicate (2 * mp + 2) 2 ++ [0])
  have H13 := (cross_back (mp + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1] ++ rep [3, 1, 0] (t + 1)) []
  have H14 := (Win.of_sweepL (sweepL_bulk (t + 1)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1])
    (List.replicate (2 * mp + 6) 2 ++ [0])
  have H15 := (Win.of_sweepL sweepL_A3 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1])
    (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
  have H16 := (Win.of_sweepL (run_ones_B (2 * m + 5)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r ++
      [1])
    ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
  have H17 := (Win.of_sweepL (sweepL_bulkB (r + 1)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0])
    (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
      (List.replicate (2 * mp + 6) 2 ++ [0]))))
  have H18 := (Win.of_sweepL sweepL_B0 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1])
    (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have H19 := (Win.of_sweepR sweepR_A0 (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1])
    (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have H20 := (Win.of_sweepL sweepL_B0 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1])
    (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have H21 := (Win.of_sweepL (run_ones_A 2) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0])
    ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
  have H22 := (Win.of_sweepL (sweepL_bulk 2) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1]
    ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))))
  have H23 := (Win.of_sweepR sweepR_02 (by simp) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1]
    ([4, 2, 0, 4] ++ ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++
      (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
        (List.replicate (2 * mp + 6) 2 ++ [0]))))))))
  have H24 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) 2) (by simp) 2).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3]
    ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
  have H25 := (cross_back 0).embed (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have H26 := p3_final.embed (by simp) []
    ([2, 2, 2, 2, 0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
      (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
        tokU 2 (2 * m + 4) ++ tokV 1 ++ rep (tokU 1 1) (t + 1) ++ tokU 1 (2 * mp + 2) ++ [0]
        : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ ([0, 4, 2] ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))) := by
    simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ ([1, 0, 3] ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3]) ++ ([0, 4, 4, 2] ++ [0]) ++
        (rep [4, 2, 0] r ++ ([4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))) := by
    simp [rep_shift']
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3]) ++ ([1, 0, 0, 3] ++ [0]) ++
        (rep [4, 2, 0] r ++ ([4, 4] ++
          (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
            ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3]) ++
        (rep [0, 4, 2] r ++ [0]) ++
        ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    simp [rep_shift']
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3]) ++
        (rep [1, 0, 3] r ++ [0]) ++
        ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++ ([0, 4, 4, 2] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [hZ]; simp
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++ ([1, 0, 0, 3] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0]) ++
        ([0, 3] ++ List.replicate (2 * (m + 1) + 1) 2) ++
        ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [show 2 * (m + 1) + 1 = 1 + (2 * m + 2) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 2)]
    simp
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0]) ++
        (List.replicate (2 * (m + 1)) 1 ++ [0, 3, 2]) ++
        ([4, 3, 2] ++ (rep [0, 4, 2] (t + 1) ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1) ++
        [0, 3, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] t ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, rep_succ]; simp
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1) ++
        [1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] t ++
          ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0, 3]) ++
        (rep [0, 4, 2] (t + 2) ++ [2]) ++ (List.replicate (2 * mp) 2 ++ [0]) := by
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ' ([0, 4, 2] : List Sym) (t + 1),
      rep_succ ([0, 4, 2] : List Sym) t,
      show 2 * mp + 2 = 2 + 2 * mp from by ring, replicate_split (2 : Sym) 2 (2 * mp)]
    simp [replicate_cons_comm]
  have E8 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0, 3]) ++
        (rep [1, 0, 3] (t + 2) ++ [2]) ++ (List.replicate (2 * mp) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0] ++
          rep [3, 1, 0] (t + 1)) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * mp + 1) 2 ++ [0])) ++ [] := by
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ' ([1, 0, 3] : List Sym) (t + 1), hY1]
    simp [rep_shift']
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1, 0] ++
          rep [3, 1, 0] (t + 1)) ++
        (3 :: (List.replicate (2 * mp + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: rep [1, 0, 3] (t + 2)) ++ (List.replicate (2 * mp + 4) 2 ++ [0]) := by
    have key : ∀ X : List Sym,
        rep [3, 1, 0] (t + 1) ++ (3 :: X) = 3 :: (rep [1, 0, 3] (t + 1) ++ X) :=
      fun X => (rep_shift' (3 : Sym) 1 0 (t + 1) X).symm
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ ([1, 0, 3] : List Sym) (t + 1)]
    simp [key]
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: rep [2, 0, 4] (t + 2)) ++ (List.replicate (2 * mp + 4) 2 ++ [0])
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        ([0, 2] ++ [0]) ++
        ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ ([2, 0, 4] : List Sym) (t + 1)]
    simp
  have E11 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        ([1, 3] ++ [0]) ++
        ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1, 3]) ++
        (rep [0, 4, 2] (t + 2) ++ [2]) ++ (List.replicate (2 * mp + 2) 2 ++ [0]) := by
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ' ([0, 4, 2] : List Sym) (t + 1), hY4]
    simp [rep_shift']
  have E12 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1, 3]) ++
        (rep [1, 0, 3] (t + 2) ++ [2]) ++ (List.replicate (2 * mp + 2) 2 ++ [0])
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1] ++
          rep [3, 1, 0] (t + 1)) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (mp + 1) + 1) 2 ++ [0])) ++ [] := by
    have key : ∀ X : List Sym,
        rep [3, 1, 0] (t + 1) ++ (3 :: X) = 3 :: (rep [1, 0, 3] (t + 1) ++ X) :=
      fun X => (rep_shift' (3 : Sym) 1 0 (t + 1) X).symm
    have kc : ∀ X : List Sym, rep [1, 0, 3] (t + 1) ++ ((1 : Sym) :: 0 :: 3 :: X)
        = 1 :: 0 :: 3 :: (rep [1, 0, 3] (t + 1) ++ X) := by
      intro X
      rw [show ((1 : Sym) :: 0 :: 3 :: X) = [1, 0, 3] ++ X from rfl, ← List.append_assoc,
        ← rep_succ' ([1, 0, 3] : List Sym) (t + 1),
        rep_succ ([1, 0, 3] : List Sym) (t + 1), List.append_assoc]
      rfl
    rw [show t + 2 = (t + 1) + 1 from by ring, rep_succ ([1, 0, 3] : List Sym) (t + 1),
      show 2 * (mp + 1) + 1 = 1 + (2 * mp + 2) from by ring,
      replicate_split (2 : Sym) 1 (2 * mp + 2)]
    simp [key, kc]
  have E13 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1] ++
          rep [3, 1, 0] (t + 1)) ++
        (3 :: (List.replicate (2 * (mp + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) ++
        (3 :: rep [1, 0, 3] (t + 1)) ++ (List.replicate (2 * mp + 6) 2 ++ [0]) := by
    rw [show 2 * (mp + 1) + 4 = 2 * mp + 6 from by ring]
    simp [rep_shift']
  have E14 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) ++
        (3 :: rep [2, 0, 4] (t + 1)) ++ (List.replicate (2 * mp + 6) 2 ++ [0])
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        [1, 3] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])) := by
    simp
  have E15 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1, 0] ++ List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        [1, 4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1]) ++ (0 :: List.replicate (2 * m + 5) 1) ++
        ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))) := by
    rw [hone]; simp
  have E16 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r ++ [1]) ++ (0 :: List.replicate (2 * m + 5) 4) ++
        ([4] ++ (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0]) ++
        (0 :: rep [3, 1, 0] (r + 1)) ++
        (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
          (List.replicate (2 * mp + 6) 2 ++ [0])))) := by
    have key : ∀ X : List Sym,
        rep [1, 0, 3] r ++ (1 :: 0 :: X) = 1 :: 0 :: (rep [3, 1, 0] r ++ X) := by
      intro X
      rw [← rep_shift' (1 : Sym) 0 3 r (0 :: X), ← rep_shift' (0 : Sym) 3 1 r X]
    rw [rep_succ ([3, 1, 0] : List Sym) r]
    simp [key]
  have E17 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0]) ++
        (0 :: rep [4, 2, 0] (r + 1)) ++
        (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
          (List.replicate (2 * mp + 6) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ [0, 0] ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    simp
  have E18 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ [0, 0] ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ ([0] ++ [0]) ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    simp
  have E19 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ ([1] ++ [0]) ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ [1, 0] ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    simp
  have E20 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1]) ++ [1, 0] ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0]) ++ (3 :: List.replicate 2 1) ++
        ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))) := by
    simp
  have E21 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0]) ++
        (3 :: List.replicate 2 2) ++
        ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ (0 :: rep [1, 0, 3] 2) ++
        ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++
          ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0]))))))) := by
    simp [rep_succ]
  have E22 : ([0, 1, 3, 1, 0, 1, 1] ++ (0 :: rep [2, 0, 4] 2) ++
        ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++
          ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0]))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ ([0, 2] ++ [0]) ++
        ([4, 2, 0, 4] ++ ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++
          (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0])))))))) := by
    simp [rep_succ]
  have E23 : ([0, 1, 3, 1, 0, 1, 1] ++ ([1, 3] ++ [0]) ++
        ([4, 2, 0, 4] ++ ([2, 2] ++ ([0] ++ (rep [4, 2, 0] (r + 1) ++
          (List.replicate (2 * m + 5) 4 ++ ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0])))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [0, 4, 2] 2 ++ [2]) ++
        ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))) := by
    simp [rep_succ]
  have E24 : ([0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [1, 0, 3] 2 ++ [2]) ++
        ([0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * 0 + 1) 2 ++ [0])) ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    simp [rep_succ]
  have E25 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        (3 :: (List.replicate (2 * 0 + 4) 2 ++ [0])) ++
        (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++ ([4] ++
          (rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
        : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        ([2, 2, 2, 2, 0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++
          ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0])))))) := by
    simp
  have E26 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        ([2, 2, 2, 2, 0] ++ (rep [4, 2, 0] (r + 1) ++ (List.replicate (2 * m + 5) 4 ++
          ([4] ++ (rep [2, 0, 4] (t + 1) ++
            (List.replicate (2 * mp + 6) 2 ++ [0])))))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) (r + 1) ++ tokU (2 * m + 6) 1 ++
        rep (tokU 1 1) t ++ tokU 1 (2 * mp + 6) ++ [0] := by
    have k1 : ∀ X : List Sym,
        rep [0, 4, 2] (r + 1) ++ (0 :: X) = 0 :: (rep [4, 2, 0] (r + 1) ++ X) :=
      fun X => (rep_shift' (0 : Sym) 4 2 (r + 1) X).symm
    have k2 : ∀ X : List Sym, rep [0, 4, 2] t ++ (0 :: X) = 0 :: (rep [4, 2, 0] t ++ X) :=
      fun X => (rep_shift' (0 : Sym) 4 2 t X).symm
    have k3 : ∀ X : List Sym, rep [4, 2, 0] t ++ (4 :: X) = 4 :: (rep [2, 0, 4] t ++ X) :=
      fun X => (rep_shift' (4 : Sym) 2 0 t X).symm
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl,
      show 2 * m + 6 = (2 * m + 5) + 1 from by ring,
      rep_succ ([2, 0, 4] : List Sym) t]
    simp [tokU, k1, k2, k3, List.replicate_succ']
  -- chain the stages
  have S1 : Win St.B St.A 3 11 _ _ 22 :=
    H1.cast (by simp) (by simp) E0.symm E1 rfl
  have S2 : Win St.A St.A 11 14 _ _ 3 :=
    H2.cast (by simp) (by simp) rfl E2 rfl
  have S3 : Win St.A St.A 14 18 _ _ 4 :=
    H3.cast (by simp) (by simp) rfl E3 rfl
  have S4 : Win St.A St.A 18 (3 * r + 18) _ _ (3 * r) :=
    H4.cast (by simp) (by simp; ring) rfl E4 (by ring)
  have S5 : Win St.A St.A (3 * r + 18) (3 * r + 22) _ _ 4 :=
    H5.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have S6 : Win St.A St.A (3 * r + 22) (3 * r + 2 * m + 24) _ _ (8 * m + 8) :=
    H6.cast (by simp; omega) (by simp; omega) rfl E6 (by ring)
  have S7 : Win St.A St.A (3 * r + 2 * m + 24) (3 * r + 2 * m + 28) _ _ 12 :=
    H7.cast (by simp; omega) (by simp; omega) rfl E7 rfl
  have S8 : Win St.A St.A (3 * r + 2 * m + 28) (3 * r + 2 * m + 3 * t + 34) _ _
      (3 * t + 6) :=
    H8.cast (by simp; omega) (by simp; omega) rfl E8 (by ring)
  have S9 : Win St.A St.A (3 * r + 2 * m + 3 * t + 34) (3 * r + 2 * m + 3 * t + 30) _ _
      (10 * mp + 14) :=
    H9.cast (by simp; omega) (by simp; omega) rfl E9 rfl
  have S10 : Win St.A St.A (3 * r + 2 * m + 3 * t + 30) (3 * r + 2 * m + 24) _ _
      (3 * t + 6) :=
    H10.cast (by simp; omega) (by simp; omega) rfl E10 (by ring)
  have S11 : Win St.A St.A (3 * r + 2 * m + 24) (3 * r + 2 * m + 26) _ _ 2 :=
    H11.cast (by simp; omega) (by simp; omega) rfl E11 rfl
  have S12 : Win St.A St.A (3 * r + 2 * m + 26) (3 * r + 2 * m + 3 * t + 32) _ _
      (3 * t + 6) :=
    H12.cast (by simp; omega) (by simp; omega) rfl E12 (by ring)
  have S13 : Win St.A St.A (3 * r + 2 * m + 3 * t + 32) (3 * r + 2 * m + 3 * t + 28) _ _
      (10 * mp + 24) :=
    H13.cast (by simp; omega) (by simp; omega) rfl E13 (by ring)
  have S14 : Win St.A St.A (3 * r + 2 * m + 3 * t + 28) (3 * r + 2 * m + 25) _ _
      (3 * t + 3) :=
    H14.cast (by simp; omega) (by simp; omega) rfl E14 (by ring)
  have S15 : Win St.A St.B (3 * r + 2 * m + 25) (3 * r + 2 * m + 24) _ _ 1 :=
    H15.cast (by simp; omega) (by simp; omega) rfl E15 rfl
  have S16 : Win St.B St.B (3 * r + 2 * m + 24) (3 * r + 19) _ _ (2 * m + 5) :=
    H16.cast (by simp; omega) (by simp; omega) rfl E16 rfl
  have S17 : Win St.B St.B (3 * r + 19) 16 _ _ (3 * r + 3) :=
    H17.cast (by simp; omega) (by simp) rfl E17 (by ring)
  have S18 : Win St.B St.A 16 15 _ _ 1 :=
    H18.cast (by simp) (by simp) rfl E18 rfl
  have S19 : Win St.A St.B 15 16 _ _ 1 :=
    H19.cast (by simp) (by simp) rfl E19 rfl
  have S20 : Win St.B St.A 16 15 _ _ 1 :=
    H20.cast (by simp) (by simp) rfl E20 rfl
  have S21 : Win St.A St.A 15 13 _ _ 2 :=
    H21.cast (by simp) (by simp) rfl E21 rfl
  have S22 : Win St.A St.A 13 7 _ _ 6 :=
    H22.cast (by simp) (by simp) rfl E22 rfl
  have S23 : Win St.A St.A 7 9 _ _ 2 :=
    H23.cast (by simp) (by simp) rfl E23 rfl
  have S24 : Win St.A St.A 9 15 _ _ 6 :=
    H24.cast (by simp) (by simp) rfl E24 rfl
  have S25 : Win St.A St.A 15 11 _ _ 14 :=
    H25.cast (by simp) (by simp) rfl E25 rfl
  have S26 : Win St.A St.B 11 0 _ _ 11 :=
    H26.cast (by simp) (by simp) rfl E26 rfl
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
  have T22 := T21.trans S23 (by simp; omega)
  have T23 := T22.trans S24 (by simp; omega)
  have T24 := T23.trans S25 (by simp; omega)
  exact (T24.trans S26 (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U21_U2b_V` is being applied. -/
theorem rule_P3_U21_U2b_V_no_halt (r m t mp : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++
      rep (tokU 1 1) r ++ tokU 2 (2 * m + 4) ++ tokV 1 ++ rep (tokU 1 1) (t + 1) ++
      tokU 1 (2 * mp + 2) ++ [0])) :
    ∀ i ≤ 167 + 6 * r + 10 * m + 12 * t + 20 * mp,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U21_U2b_V r m t mp).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
