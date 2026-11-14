import RequestProject.Flat

/-!
# The `P1` rule over an arbitrary flat block sequence

`Flat.lean` proved the `P3` macro rule for a tape word in which, after the first token
`U(2,1)`, the blocks `U(kᵢ,1)` may have arbitrary exponents `kᵢ ∈ {1,2}` in any order.
This file proves the `P1` half of the same statement:

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2) 0
          --(91 + 12r + 10m + ∑ (4kᵢ + 2)) steps-->
      U(2,2) u · U(2,1) · u^r · U(1,4) · U(1,k₁) ⋯ U(1,kₙ) · U(1,2m+4) 0
```

The step count is exactly the same as in the `P3` case; the two rules differ only in the
fixed prologue and epilogue at the left end (and in the fact that the `P1` prologue raises
the first `u` to `U(2,1)`).  Together with `rule_P2`, which is unconditional, these two
rules cover every macro step of the machine whose carry meets only tokens `U(1,1)`,
`U(2,1)` and an absorbing token `U(1,2m+2)`.
-/

namespace BB25

/-- **The `P1` rule over an arbitrary flat block sequence.**  The head is in state `B` on
the leftmost non-blank cell, with three blank cells to its left, and the tape reads
`U(2,1) U(4,1) · U(1,1)^(r+1) · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2)` followed by the `0`
of the next token, where every `kᵢ` is `1` or `2`.  In exactly
`91 + 12r + 10m + ∑ (4kᵢ + 2)` steps the machine raises the first `u` to `U(2,1)`, turns
the token `U(2,1)` into `U(1,4)`, carries the remaining two `2`s past all the blocks
`U(kᵢ,1)` into the absorbing token, and arrives, again in state `B`, on the new leftmost
non-blank cell three cells further left.  Nothing outside the window is read or written. -/
theorem rule_P1_flat (r m : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k = 1 ∨ k = 2) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        wordIn ks ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ outW ks ++
        tokU 1 (2 * m + 4) ++ [0])
      (91 + 12 * r + 10 * m + cost ks + costL ks) := by
  -- splitting off leading `2`s from the run of `2`s
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  -- the block `U(2,1)` crossed rightwards, then the flat block sequence
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  have hCD : SweepR St.A St.A
      ([0, 4, 4, 2] ++ (wordIn ks ++ [0, 4, 2])) ([1, 0, 0, 3] ++ (wordOut ks ++ [1, 0, 3]))
      (4 + (cost ks + 3)) :=
    hblk.comp ((sweepR_blocks ks).comp sweepR_042 (by simp)) (by simp)
  -- stage A : the opening
  have HA := p1g_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))))
  -- stage B : the carry crosses the run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3]
    ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++ (List.replicate (2 * m + 1) 2 ++ [0])))
  -- stages C+D : the `U(2,1)` block and the flat block sequence
  have HCD := (Win.of_sweepR hCD (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1))
    (List.replicate (2 * m) 2 ++ [0])
  -- stage E : the round trip through the run of `2`s
  have HE := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
      wordOutS ks) []
  -- stage F : back across the flat block sequence
  have HF := (Win.of_sweepL (sweepL_blocks_small ks hks) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage G : back across the `U(2,1)` block
  have HG := (Win.of_sweepL blockL_1003 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage H : back across the run of `u`s
  have HH := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0]
    ([2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage I : the reflection at the `4`-run of the prefix
  have HI := p1g_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    (rep [2, 0, 4] (r + 1) ++ ([2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0]))))
  -- stage J : one step to the right
  have HJ := p1g_B4.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0])))))
  -- stage K : the second rightward crossing of the run of `u`s
  have HK := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0]
    ([2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage L : the reflection at the `U(2,1)` block
  have HL := u21_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r)
    (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage M : the last leftward crossing
  have HM := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0]
    ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage N : the last `u` becomes `U(2,1)`
  have HN := p1g_back.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1]
    (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0]))))
  -- stage O : the closing
  have HO := p1g_close.embed (by simp) []
    ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0])))))
  -- the sixteen tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        wordIn ks ++ tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++
          (List.replicate (2 * m + 1) 2 ++ [0]))) := by
    rw [rep_succ ([0, 4, 2] : List Sym) r, q2, q1]
    simp
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++
          (List.replicate (2 * m + 1) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([0, 4, 4, 2] ++ (wordIn ks ++ [0, 4, 2])) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q1]; simp
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([1, 0, 0, 3] ++ (wordOut ks ++ [1, 0, 3])) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          wordOutS ks) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [q1]; simp [shift_wordOut]
  have E4 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 0] ++ wordOutS ks) ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: wordOut ks) ++ (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp [shift_wordOut]
  have E5 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] (r + 1) ++
          [1, 0, 0]) ++
        (3 :: wordBack ks) ++ (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [1, 0, 0, 3]) ++
        (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have E6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [2, 2, 0, 4]) ++
        (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        ([2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E7 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3] ++
        (rep [2, 0, 4] (r + 1) ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) := by
    simp
  have E8 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 3, 1, 4] ++
        (rep [2, 0, 4] (r + 1) ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [4, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) := by
    rw [rep_succ]; simp
  have E9 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ]; simp
  have E10 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        [3, 1, 0, 2, 2, 0] ++
        (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        [3, 2, 2, 2, 2, 0] ++
        (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    simp [rep_shift']
  have E12 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) := by
    simp
  have E13 : ([0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0] ++
        ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) := by
    simp
  have E14 : ([] ++ [0, 4, 4, 2, 2, 0, 4, 2, 0] ++
        ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ outW ks ++
        tokU 1 (2 * m + 4) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, rep_shift']
    exact shift_wordBack ks _
  -- chain the stages
  have SA : Win St.B St.A 3 13 _ _ 16 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 13 (3 * r + 16) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SCD : Win St.A St.A (3 * r + 16) (3 * r + cost ks + 23) _ _ (cost ks + 7) :=
    HCD.cast (by simp; omega) (by simp; omega) rfl E3 (by omega)
  have SE : Win St.A St.A (3 * r + cost ks + 23) (3 * r + cost ks + 19) _ _ (10 * m + 14) :=
    HE.cast (by simp; omega) (by simp; omega) rfl E4 rfl
  have SF : Win St.A St.A (3 * r + cost ks + 19) (3 * r + 19) _ _ (costL ks) :=
    HF.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have SG : Win St.A St.A (3 * r + 19) (3 * r + 15) _ _ 6 :=
    HG.cast (by simp; omega) (by simp; omega) rfl E6 rfl
  have SH : Win St.A St.A (3 * r + 15) 12 _ _ (3 * r + 3) :=
    HH.cast (by simp; omega) (by simp) rfl E7 (by ring)
  have SI : Win St.A St.B 12 12 _ _ 8 :=
    HI.cast (by simp) (by simp) rfl E8 rfl
  have SJ : Win St.B St.B 12 13 _ _ 1 :=
    HJ.cast (by simp) (by simp) rfl E9 rfl
  have SK : Win St.B St.B 13 (3 * r + 16) _ _ (3 * r + 3) :=
    HK.cast (by simp) (by simp; ring) rfl E10 (by ring)
  have SL : Win St.B St.A (3 * r + 16) (3 * r + 13) _ _ 15 :=
    HL.cast (by simp; omega) (by simp; omega) rfl E11 rfl
  have SM : Win St.A St.A (3 * r + 13) 13 _ _ (3 * r) :=
    HM.cast (by simp; omega) (by simp) rfl E12 (by ring)
  have SN : Win St.A St.B 13 8 _ _ 5 :=
    HN.cast (by simp) (by simp) rfl E13 rfl
  have SO : Win St.B St.B 8 0 _ _ 10 :=
    HO.cast (by simp) (by simp) rfl E14 rfl
  have T1 := SA.trans SB (by simp; omega)
  have T2 := T1.trans SCD (by simp; omega)
  have T3 := T2.trans SE (by simp; omega)
  have T4 := T3.trans SF (by simp; omega)
  have T5 := T4.trans SG (by simp; omega)
  have T6 := T5.trans SH (by simp; omega)
  have T7 := T6.trans SI (by simp; omega)
  have T8 := T7.trans SJ (by simp; omega)
  have T9 := T8.trans SK (by simp; omega)
  have T10 := T9.trans SL (by simp; omega)
  have T11 := T10.trans SM (by simp; omega)
  have T12 := T11.trans SN (by simp; omega)
  exact (T12.trans SO (by simp; omega)).cast rfl rfl rfl rfl (by omega)

/-- The machine does not halt while `rule_P1_flat` is being applied. -/
theorem rule_P1_flat_no_halt (r m : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k = 1 ∨ k = 2)
    (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 2 1 ++ wordIn ks ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 12 * r + 10 * m + cost ks + costL ks,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1_flat r m ks hks).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
