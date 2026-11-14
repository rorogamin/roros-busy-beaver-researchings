import RequestProject.CarryP1V

/-!
# A crossed `U(2,1)` and an absorbing `U(2,b)` at once

The census of `ANALYSIS.md` §31 contains a row in which *both* of the two complications
occur in the same macro step: one of the tokens the rightward pass crosses has exponent
`a = 2` (so the *second* pass is stopped by it, as in `rule_P3_U21`) and the token that
absorbs the carry is a `U(2,b)` (so it splits, as in `rule_P3_U2b`).  In the real orbit the
crossed block sequence of that row is always `U(2,1) u u u`, i.e. the exponent-`2` block
comes first; the rule below is proved for `U(2,1) u^r` with an arbitrary `r`.

```
0 0 0 · U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) 0
       --(107 + 6r + 10m) steps-->
   U(2,1) U(4,1) · U(1,4) · u^r · U(1,2) V(2m+3) 0
```

This rule is **short** and its window stops at the first cell after the absorbing token:
the carry never gets past that token, so whatever stands to the right of it is irrelevant
and untouched — in contrast with every earlier rule of the development, in which a carry of
two or four `2`s had to be carried on to the following tokens.  The reason is the crossed
`U(2,1)`: the second pass is turned around by it (`u21_turn`), so the absorbing token is
visited only once, by the first pass, which splits it into `U(1,2) V(2m+3)` and stops.

Every piece of the proof already exists: `carry_open`, `blockR 2`, `sweepR_042`,
`turn_U2`, `retU2`, `blockL_1003`, `sweepL_103`, `carry_reflect`, `sweepR_204`,
`u21_turn` and `p3_final`.  The computation is exhibited as fourteen macro steps.
-/

namespace BB25

/-- **The `P3` rule with a crossed `U(2,1)` and an absorbing `U(2,2m+4)`.**  The head is in
state `B` on the leftmost non-blank cell, with three blank cells to its left, and the tape
reads

`U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4)`

followed by the `0` of the next token.  In exactly `107 + 6r + 10m` steps the absorbing
token splits into `U(1,2) V(2m+3)`, the crossed `U(2,1)` becomes `U(1,4)`, the prefix
becomes `U(2,1) U(4,1)`, and the head arrives, again in state `B`, on the new leftmost
non-blank cell three cells further left.  Nothing outside the window is read or written —
in particular nothing beyond the absorbing token. -/
theorem rule_P3_U21_U2b (r m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
        tokU 2 (2 * m + 4) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) r ++ tokU 1 2 ++
        tokV (2 * m + 3) ++ [0])
      (107 + 6 * r + 10 * m) := by
  -- splitting the run of `2`s of the absorbing token
  have hz2 : List.replicate (2 * m + 4) (2 : Sym) = [2, 2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 4 = 2 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hz3 : List.replicate (2 * m + 3) (2 : Sym) = [2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hz4 : List.replicate (2 * m + 4) (2 : Sym) = [2] ++ List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  -- the block `U(2,·)` crossed rightwards
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  -- the fourteen stages
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++
      ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])))))
  have HB1 := (Win.of_sweepR sweepR_042 (by simp) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))))
  have HB2 := (Win.of_sweepR hblk (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3])
    (rep [4, 2, 0] r ++ ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  have HB3 := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) r) (by simp) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3])
    ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  have HC := (Win.of_sweepR hblk (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r)
    (List.replicate (2 * m + 2) 2 ++ [0])
  have HD := (turn_U2 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++ rep [1, 0, 3] r) []
  have HE := (Win.of_sweepL retU2 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0] ++ rep [3, 1, 0] r)
    (List.replicate (2 * m + 3) 2 ++ [0])
  have HF := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0])
    ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))
  have HG := (Win.of_sweepL blockL_1003 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0])
    (rep [2, 0, 4] r ++ ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))
  have HH := (Win.of_sweepL sweepL_103 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
      ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))
  have HI := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
      ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))))
  have HJ := (Win.of_sweepR sweepR_204 (by simp) 2).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 0, 4] ++ (rep [2, 0, 4] r ++
      ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))
  have HK := u21_turn.embed (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([4] ++ (rep [2, 0, 4] r ++ ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))
  have HL := p3_final.embed (by simp) []
    ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
      ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
        tokU 2 (2 * m + 4) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++
          ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] r ++
          ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ ([0, 4, 2] ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] r ++
          ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])))) := by
    simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ ([1, 0, 3] ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] r ++
          ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3]) ++ ([0, 4, 4, 2] ++ [0]) ++
        (rep [4, 2, 0] r ++ ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    simp [rep_shift']
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3]) ++ ([1, 0, 0, 3] ++ [0]) ++
        (rep [4, 2, 0] r ++ ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3]) ++
        (rep [0, 4, 2] r ++ [0]) ++ ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    simp [rep_shift']
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3]) ++
        (rep [1, 0, 3] r ++ [0]) ++
        ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++ ([0, 4, 4, 2] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [hz2]; simp
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++ ([1, 0, 0, 3] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++
        ([1, 0, 0, 3] ++ List.replicate (2 * (m + 1) + 1) 2 ++ [0]) ++ [] := by
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, hz3]; simp
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0, 3] ++
          rep [1, 0, 3] r) ++
        ([1, 1, 3] ++ List.replicate (2 * (m + 1) + 2) 2 ++ [0]) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0] ++
          rep [3, 1, 0] r) ++ (3 :: [1, 1, 3, 2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) := by
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 from by ring, hz4]
    simp [rep_shift']
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0] ++
          rep [3, 1, 0] r) ++ (3 :: [2, 2, 4, 3]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0]) ++
        (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])) := by
    simp [rep_shift']
  have E8 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0, 3] ++ [1, 0, 0]) ++
        (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0]) ++ (3 :: [1, 0, 0, 3]) ++
        (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))) := by
    simp
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ [1, 0]) ++ (3 :: [2, 2, 0, 4]) ++
        (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: [1, 0, 3]) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) := by
    simp
  have E10 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: [2, 0, 4]) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))) := by
    simp
  have E11 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ ([2, 0, 4] ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) := by
    simp
  have E12 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ ([3, 1, 0] ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ [3, 1, 0, 2, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) := by
    simp
  have E13 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ [3, 2, 2, 2, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) := by
    simp
  have E14 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) r ++ tokU 1 2 ++
        tokV (2 * m + 3) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB1 : Win St.A St.A 11 14 _ _ 3 :=
    HB1.cast (by simp) (by simp) rfl E2 rfl
  have SB2 : Win St.A St.A 14 18 _ _ 4 :=
    HB2.cast (by simp) (by simp) rfl E3 rfl
  have SB3 : Win St.A St.A 18 (3 * r + 18) _ _ (3 * r) :=
    HB3.cast (by simp) (by simp; ring) rfl E4 (by ring)
  have SC : Win St.A St.A (3 * r + 18) (3 * r + 22) _ _ 4 :=
    HC.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have SD : Win St.A St.A (3 * r + 22) (3 * r + 21) _ _ (10 * m + 25) :=
    HD.cast (by simp; omega) (by simp; omega) rfl E6 (by ring)
  have SE : Win St.A St.A (3 * r + 21) (3 * r + 17) _ _ 4 :=
    HE.cast (by simp; omega) (by simp; omega) rfl E7 rfl
  have SF : Win St.A St.A (3 * r + 17) 17 _ _ (3 * r) :=
    HF.cast (by simp; omega) (by simp) rfl E8 (by ring)
  have SG : Win St.A St.A 17 13 _ _ 6 :=
    HG.cast (by simp) (by simp) rfl E9 rfl
  have SH : Win St.A St.A 13 10 _ _ 3 :=
    HH.cast (by simp) (by simp) rfl E10 rfl
  have SI : Win St.A St.B 10 11 _ _ 7 :=
    HI.cast (by simp) (by simp) rfl E11 rfl
  have SJ : Win St.B St.B 11 14 _ _ 3 :=
    HJ.cast (by simp) (by simp) rfl E12 rfl
  have SK : Win St.B St.A 14 11 _ _ 15 :=
    HK.cast (by simp) (by simp) rfl E13 rfl
  have SL : Win St.A St.B 11 0 _ _ 11 :=
    HL.cast (by simp) (by simp) rfl E14 rfl
  have T1 := SA.trans SB1 (by simp; omega)
  have T2 := T1.trans SB2 (by simp; omega)
  have T3 := T2.trans SB3 (by simp; omega)
  have T4 := T3.trans SC (by simp; omega)
  have T5 := T4.trans SD (by simp; omega)
  have T6 := T5.trans SE (by simp; omega)
  have T7 := T6.trans SF (by simp; omega)
  have T8 := T7.trans SG (by simp; omega)
  have T9 := T8.trans SH (by simp; omega)
  have T10 := T9.trans SI (by simp; omega)
  have T11 := T10.trans SJ (by simp; omega)
  have T12 := T11.trans SK (by simp; omega)
  exact (T12.trans SL (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U21_U2b` is being applied. -/
theorem rule_P3_U21_U2b_no_halt (r m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 1 ++
      rep (tokU 1 1) r ++ tokU 2 (2 * m + 4) ++ [0])) :
    ∀ i ≤ 107 + 6 * r + 10 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U21_U2b r m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
