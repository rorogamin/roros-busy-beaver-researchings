import RequestProject.CarryU21

/-!
# The carry crossing an arbitrary flat block sequence

All the macro rules proved so far describe the carry crossing a *run* of equal tokens:
`rule_P3_gen` a run of `u = U(1,1)`, `rule_P3_U21` a run of `u`, then a single `U(2,1)`,
then another run of `u`.  This file proves the rule for an **arbitrary interleaving**:
after the first `U(2,1)` the tape may carry any sequence of tokens `U(1,1)` and `U(2,1)`,
in any order.

```
0 0 0 · U(2,2) V(1) U(1,1) · u^r · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2) 0
          --(91 + 12r + 10m + ∑ (4kᵢ + 2)) steps-->
      U(2,1) U(4,1) · u^r · U(1,4) · U(1,k₁) ⋯ U(1,kₙ) · U(1,2m+4) 0
```

for every `r, m` and every list `k₁, …, kₙ` of exponents with `kᵢ ∈ {1, 2}`.  This is the
first rule of the development in which the *shape* of the tape word, and not merely the
length of a run, is arbitrary.

The mechanism is the two-pass structure of a macro step.  The first pass sweeps rightwards
over all the blocks `0 4^k 2` (`sweepR_blocks`, which is already valid for arbitrary
exponents), deposits two `2`s in the absorbing token (`cross_back`) and returns leftwards;
on the way back a block `1 0 3` becomes `2 0 4` and a block `1 0 0 3` becomes `2 2 0 4`
(`sweepL_blocks_small` below).  The second pass, in state `B`, is stopped by the *first*
`2 2` it meets, i.e. by the first block with exponent `2`; that block absorbs the other two
`2`s and becomes `U(1,4)` (`u21_turn`).  Every later block is therefore crossed exactly
once in each direction, and is simply re-read with a shifted token boundary:
`U(k,1) = 0 4^k 2` becomes `2^k 0 4`, which the new alignment reads as `U(1,k)`.
-/

namespace BB25

/-! ### The leftward pass over a flat block sequence -/

/-- What a leftward pass in state `A` leaves behind on the block `1 0^k 3`, namely
`2^k 0 4`.  (For `k ≥ 3` there is no such word: the head is reflected instead.) -/
def blkBack (k : ℕ) : List Sym := List.replicate k 2 ++ [0, 4]

/-- The word `blkOut k = 1 0^k 3` read one cell later, namely `3 1 0^k`. -/
def blkOutS (k : ℕ) : List Sym := [3, 1] ++ List.replicate k 0

/-- The tape word a leftward pass leaves behind on a block sequence. -/
def wordBack (ks : List ℕ) : List Sym := (ks.map blkBack).flatten

/-- The tape word of a block sequence after a rightward pass, read one cell later. -/
def wordOutS (ks : List ℕ) : List Sym := (ks.map blkOutS).flatten

/-- The tokens the blocks have become when the macro step is over. -/
def outW (ks : List ℕ) : List Sym := (ks.map (tokU 1)).flatten

/-- The cost of a leftward pass over a block sequence. -/
def costL (ks : List ℕ) : ℕ := (ks.map (fun k => 3 * k)).sum

@[simp] lemma blkBack_length (k : ℕ) : (blkBack k).length = k + 2 := by
  simp [blkBack]

@[simp] lemma blkOutS_length (k : ℕ) : (blkOutS k).length = k + 2 := by
  simp [blkOutS]

@[simp] lemma wordBack_nil : wordBack [] = [] := rfl
@[simp] lemma wordOutS_nil : wordOutS [] = [] := rfl
@[simp] lemma outW_nil : outW [] = [] := rfl
@[simp] lemma costL_nil : costL [] = 0 := rfl

lemma wordBack_cons (k : ℕ) (ks : List ℕ) :
    wordBack (k :: ks) = blkBack k ++ wordBack ks := rfl
lemma wordOutS_cons (k : ℕ) (ks : List ℕ) :
    wordOutS (k :: ks) = blkOutS k ++ wordOutS ks := rfl
lemma outW_cons (k : ℕ) (ks : List ℕ) :
    outW (k :: ks) = tokU 1 k ++ outW ks := rfl
lemma costL_cons (k : ℕ) (ks : List ℕ) : costL (k :: ks) = 3 * k + costL ks := rfl

@[simp] lemma wordIn_length (ks : List ℕ) : (wordIn ks).length = cost ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [wordIn_cons, List.length_append, ih, blkIn_length, cost_cons]

@[simp] lemma wordOut_length (ks : List ℕ) : (wordOut ks).length = cost ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [wordOut_cons, List.length_append, ih, blkOut_length, cost_cons]

@[simp] lemma wordBack_length (ks : List ℕ) : (wordBack ks).length = cost ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [wordBack_cons, List.length_append, ih, blkBack_length, cost_cons]

@[simp] lemma wordOutS_length (ks : List ℕ) : (wordOutS ks).length = cost ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [wordOutS_cons, List.length_append, ih, blkOutS_length, cost_cons]

@[simp] lemma outW_length (ks : List ℕ) : (outW ks).length = cost ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [outW_cons, List.length_append, ih, tokU_length, cost_cons]; omega

/-- **The leftward block rule.**  A block `1 0 3` or `1 0 0 3` is crossed leftwards in
state `A` in `3k` steps, and becomes `2^k 0 4`. -/
theorem sweepL_blk_small {k : ℕ} (h : k = 1 ∨ k = 2) :
    SweepL St.A St.A (blkOut k) (blkBack k) (3 * k) := by
  rcases h with rfl | rfl
  · exact (show SweepL St.A St.A [1, 0, 3] [2, 0, 4] 3 from sweepL_103)
  · exact (show SweepL St.A St.A [1, 0, 0, 3] [2, 2, 0, 4] 6 from blockL_1003)

/-- **The leftward pass.**  A sequence of blocks with exponents `1` and `2` is crossed
leftwards in state `A`, in one pass, in `∑ 3kᵢ` steps. -/
theorem sweepL_blocks_small : ∀ (ks : List ℕ), (∀ k ∈ ks, k = 1 ∨ k = 2) →
    SweepL St.A St.A (wordOut ks) (wordBack ks) (costL ks) := by
  intro ks
  induction ks with
  | nil => intro _; simpa using sweepL_nil St.A
  | cons k ks ih =>
      intro h
      have hk : k = 1 ∨ k = 2 := h k (by simp)
      have hks : ∀ j ∈ ks, j = 1 ∨ j = 2 := fun j hj => h j (by simp [hj])
      have hc : costL (k :: ks) = costL ks + 3 * k := by rw [costL_cons]; ring
      rw [wordOut_cons, wordBack_cons, hc]
      exact (ih hks).comp (sweepL_blk_small hk) (by simp)

/-! ### Re-reading the block sequence with a shifted boundary -/

lemma shift_wordOut (ks : List ℕ) (rest : List Sym) :
    (3 : Sym) :: (wordOut ks ++ rest) = wordOutS ks ++ ((3 : Sym) :: rest) := by
  induction ks generalizing rest with
  | nil => simp
  | cons k ks ih =>
      rw [wordOut_cons, wordOutS_cons, List.append_assoc]
      show (3 : Sym) :: (blkOut k ++ (wordOut ks ++ rest)) = _
      rw [← List.cons_append]
      have e : (3 : Sym) :: blkOut k = blkOutS k ++ [3] := by
        simp [blkOut, blkOutS]
      rw [e, List.append_assoc, List.append_assoc]
      congr 1
      rw [← List.append_assoc]
      show ([3] ++ (wordOut ks ++ rest) : List Sym) = _
      rw [← ih]
      rfl

lemma shift_wordBack (ks : List ℕ) (rest : List Sym) :
    ([0, 4] : List Sym) ++ (wordBack ks ++ rest) = outW ks ++ (([0, 4] : List Sym) ++ rest) := by
  induction ks generalizing rest with
  | nil => simp
  | cons k ks ih =>
      have e : ([0, 4] : List Sym) ++ blkBack k = tokU 1 k ++ [0, 4] := by
        simp [blkBack, tokU]
      calc ([0, 4] : List Sym) ++ (wordBack (k :: ks) ++ rest)
          = (([0, 4] : List Sym) ++ blkBack k) ++ (wordBack ks ++ rest) := by
            rw [wordBack_cons]; simp
        _ = tokU 1 k ++ (([0, 4] : List Sym) ++ (wordBack ks ++ rest)) := by
            rw [e]; simp
        _ = tokU 1 k ++ (outW ks ++ (([0, 4] : List Sym) ++ rest)) := by rw [ih]
        _ = outW (k :: ks) ++ (([0, 4] : List Sym) ++ rest) := by
            rw [outW_cons]; simp

/-! ### The rule -/

/-- **The `P3` rule over an arbitrary flat block sequence.**  The head is in state `B` on
the leftmost non-blank cell, with three blank cells to its left, and the tape reads

`U(2,2) V(1) U(1,1) · U(1,1)^r · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2)`

followed by the `0` of the next token, where every `kᵢ` is `1` or `2`.  In exactly
`91 + 12r + 10m + ∑ (4kᵢ + 2)` steps the machine turns the first `U(2,1)` into `U(1,4)`,
carries the remaining two `2`s past all the blocks `U(kᵢ,1)` into `U(1,2m+2)`, re-reads
each `U(kᵢ,1)` as `U(1,kᵢ)`, and arrives, again in state `B`, on the new leftmost non-blank
cell three cells further left.  Nothing outside the window is read or written.

This contains `rule_P3_gen`'s successor `rule_P3_U21` as the special case
`k₁ = ⋯ = kₙ = 1`, and is the first rule of the development valid for an arbitrary *shape*
of the tape word. -/
theorem rule_P3_flat (r m : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k = 1 ∨ k = 2) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        wordIn ks ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ outW ks ++
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
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))))
  -- stage B : the carry crosses the run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++ (List.replicate (2 * m + 1) 2 ++ [0])))
  -- stages C+D : the `U(2,1)` block and the flat block sequence
  have HCD := (Win.of_sweepR hCD (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1))
    (List.replicate (2 * m) 2 ++ [0])
  -- stage E : the round trip through the run of `2`s
  have HE := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
      wordOutS ks) []
  -- stage F : back across the flat block sequence
  have HF := (Win.of_sweepL (sweepL_blocks_small ks hks) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage G : back across the `U(2,1)` block
  have HG := (Win.of_sweepL blockL_1003 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage H : back across the run of `u`s
  have HH := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    ([2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage I : the reflection at the `4`-run of the prefix
  have HI := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0])))))
  -- stage J : the second rightward crossing of the run of `u`s
  have HJ := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage K : the reflection at the `U(2,1)` block
  have HK := u21_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r)
    (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage L : the last leftward crossing
  have HL := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage M : the closing
  have HM := p3_final.embed (by simp) []
    (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
      (List.replicate (2 * m + 4) 2 ++ [0]))))
  -- the fourteen tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        wordIn ks ++ tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (wordIn ks ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++
          (List.replicate (2 * m + 1) 2 ++ [0]))) := by
    rw [rep_succ ([0, 4, 2] : List Sym) r, q2, q1]
    simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ ((wordIn ks ++ [0, 4, 2]) ++
          (List.replicate (2 * m + 1) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([0, 4, 4, 2] ++ (wordIn ks ++ [0, 4, 2])) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q1]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([1, 0, 0, 3] ++ (wordOut ks ++ [1, 0, 3])) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          wordOutS ks) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [q1]; simp [shift_wordOut]
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          wordOutS ks) ++ (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: wordOut ks) ++ (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp [shift_wordOut]
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: wordBack ks) ++ (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [1, 0, 0, 3]) ++
        (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [2, 2, 0, 4]) ++
        (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        ([2, 2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E7 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) := by
    rw [rep_succ]; simp
  have E8 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ]; simp
  have E9 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++ [3, 1, 0, 2, 2, 0] ++
        (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        [3, 2, 2, 2, 2, 0] ++
        (4 :: (wordBack ks ++ (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    simp [rep_shift']
  have E11 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) := by
    simp
  have E12 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (wordBack ks ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ outW ks ++
        tokU 1 (2 * m + 4) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, rep_shift']
    exact shift_wordBack ks _
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SCD : Win St.A St.A (3 * r + 14) (3 * r + cost ks + 21) _ _ (cost ks + 7) :=
    HCD.cast (by simp; omega) (by simp; omega) rfl E3 (by omega)
  have SE : Win St.A St.A (3 * r + cost ks + 21) (3 * r + cost ks + 17) _ _ (10 * m + 14) :=
    HE.cast (by simp; omega) (by simp; omega) rfl E4 rfl
  have SF : Win St.A St.A (3 * r + cost ks + 17) (3 * r + 17) _ _ (costL ks) :=
    HF.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have SG : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ 6 :=
    HG.cast (by simp; omega) (by simp; omega) rfl E6 rfl
  have SH : Win St.A St.A (3 * r + 13) 10 _ _ (3 * r + 3) :=
    HH.cast (by simp; omega) (by simp) rfl E7 (by ring)
  have SI : Win St.A St.B 10 11 _ _ 7 :=
    HI.cast (by simp) (by simp) rfl E8 rfl
  have SJ : Win St.B St.B 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HJ.cast (by simp) (by simp; ring) rfl E9 (by ring)
  have SK : Win St.B St.A (3 * r + 14) (3 * r + 11) _ _ 15 :=
    HK.cast (by simp; omega) (by simp; omega) rfl E10 rfl
  have SL : Win St.A St.A (3 * r + 11) 11 _ _ (3 * r) :=
    HL.cast (by simp; omega) (by simp) rfl E11 (by ring)
  have SM : Win St.A St.B 11 0 _ _ 11 :=
    HM.cast (by simp) (by simp) rfl E12 rfl
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
  exact (T10.trans SM (by simp; omega)).cast rfl rfl rfl rfl (by omega)

/-- The total cost of the flat block sequence: `∑ (4kᵢ + 2)`. -/
lemma cost_add_costL (ks : List ℕ) :
    cost ks + costL ks = (ks.map (fun k => 4 * k + 2)).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      rw [cost_cons, costL_cons, List.map_cons, List.sum_cons, ← ih]; ring

/-- The machine does not halt while `rule_P3_flat` is being applied. -/
theorem rule_P3_flat_no_halt (r m : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k = 1 ∨ k = 2)
    (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
      wordIn ks ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 12 * r + 10 * m + cost ks + costL ks,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_flat r m ks hks).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
