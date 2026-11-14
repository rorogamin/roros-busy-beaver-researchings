import RequestProject.Fractal

/-!
# The carry crossing a token `U(2,1)`

`Carry.lean` and `CarryP1.lean` proved the two left-end rules in the case in which the
carry of four `2`s meets nothing but tokens `u = U(1,1)` before it is absorbed.  The next
case of the "carry table" of `ANALYSIS.md` §19 is a token `U(2,1)`:  the carry turns it
into `U(1,4)` and **two** of the four `2`s travel on, to be absorbed by the next token
with more than one `2`.  This file proves that rule, in the phase `P3` and with arbitrary
runs of `u` tokens on either side of the `U(2,1)`:

```
0 0 0 · U(2,2) V(1) U(1,1) · u^r · U(2,1) · u^s · U(1,2m+2) 0
              --(91 + 12r + 6s + 10m) steps-->
        U(2,1) U(4,1) · u^r · U(1,4) · u^s · U(1,2m+4) 0
```

The proof exhibits the computation as thirteen macro steps.  The head crosses the run
`u^r` four times and the run `u^s` twice; it crosses the `U(2,1)` block rightwards as the
block rule `blockR 2` and leftwards as `blockL_1003`; it makes one round trip through the
run of `2`s (`cross_back`); and it is reflected twice, once at the `4`-run of the prefix
(`carry_reflect`) and once at the `U(2,1)` block itself — the fifteen-step piece
`u21_turn` below, which is where the two `2`s are deposited and `U(2,1)` becomes `U(1,4)`.

Together with `rule_P1_gen` and `rule_P3_gen` this makes the first three rows of the carry
table machine-checked for arbitrary surroundings.
-/

namespace BB25

/-! ### The one new fixed piece -/

/-- **The reflection at a `U(2,1)` token.**  The head, sweeping rightwards in state `B`
over the block `2 2 0 4` that a `U(2,1)` token has become, is turned around after fifteen
steps, leaving `2 2 2 2`: the two `2`s of the carry have been deposited and the token
`U(2,1)` has become `U(1,4)`. -/
theorem u21_turn : Win St.B St.A 3 0 [3, 1, 0, 2, 2, 0] [3, 2, 2, 2, 2, 0] 15 :=
  Win.of_lrun (by decide)

/-! ### The rule -/

/-- **The `P3` rule with a `U(2,1)` in the way.**  The head is in state `B` on the leftmost
non-blank cell, with three blank cells to its left, and the tape reads
`U(2,2) V(1) U(1,1) · U(1,1)^r · U(2,1) · U(1,1)^s · U(1,2m+2)` followed by the `0` of the
next token.  In exactly `91 + 12r + 6s + 10m` steps the machine turns `U(2,1)` into
`U(1,4)`, carries the remaining two `2`s through the `s` tokens `u` into `U(1,2m+2)`, and
arrives, again in state `B`, on the new leftmost non-blank cell three cells further left,
the tape now reading `U(2,1) U(4,1) · U(1,1)^r · U(1,4) · U(1,1)^s · U(1,2m+4)`.  Nothing
outside the window is read or written, so the rest of the tape is arbitrary. -/
theorem rule_P3_U21 (r s m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ rep (tokU 1 1) s ++
        tokU 1 (2 * m + 4) ++ [0])
      (91 + 12 * r + 6 * s + 10 * m) := by
  -- splitting off leading `2`s from the run of `2`s
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  -- the block `U(2,1)` crossed rightwards, then the following run of `u`s
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  have hCD : SweepR St.A St.A
      ([0, 4, 4, 2] ++ rep [0, 4, 2] (s + 1)) ([1, 0, 0, 3] ++ rep [1, 0, 3] (s + 1))
      (4 + (s + 1) * 3) :=
    hblk.comp (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp)
  -- stage A : the opening
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
      ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))))
  -- stage B : the carry crosses the first run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++ (List.replicate (2 * m + 1) 2 ++ [0])))
  -- stages C+D : the `U(2,1)` block and the second run of `u`s
  have HCD := (Win.of_sweepR hCD (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1))
    (List.replicate (2 * m) 2 ++ [0])
  -- stage E : the round trip through the run of `2`s
  have HE := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
      rep [3, 1, 0] s) []
  -- stage F : back across the second run of `u`s
  have HF := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0])
    (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage G : back across the `U(2,1)` block
  have HG := (Win.of_sweepL blockL_1003 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage H : back across the first run of `u`s
  have HH := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage I : the reflection at the `4`-run of the prefix
  have HI := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
      (List.replicate (2 * m + 4) 2 ++ [0])))))
  -- stage J : the second rightward crossing of the first run of `u`s
  have HJ := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage K : the reflection at the `U(2,1)` block
  have HK := u21_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r)
    (4 :: (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage L : the last leftward crossing
  have HL := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage M : the closing
  have HM := p3_final.embed (by simp) []
    (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
      (List.replicate (2 * m + 4) 2 ++ [0]))))
  -- the fourteen tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
        rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4, 2] ++ (rep [0, 4, 2] s ++
          ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++ (List.replicate (2 * m + 1) 2 ++ [0]))) := by
    rw [rep_succ ([0, 4, 2] : List Sym) r, rep_succ' ([0, 4, 2] : List Sym) s, q2, q1]
    simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4, 2] ++ (rep [0, 4, 2] (s + 1) ++
          (List.replicate (2 * m + 1) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([0, 4, 4, 2] ++ rep [0, 4, 2] (s + 1)) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [q1]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        (([1, 0, 0, 3] ++ rep [1, 0, 3] (s + 1)) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ' ([1, 0, 3] : List Sym) s, q1]; simp [rep_shift']
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0] ++
          rep [3, 1, 0] s) ++ (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: rep [1, 0, 3] s) ++ (List.replicate (2 * m + 4) 2 ++ [0]) := by
    simp [rep_shift']
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1) ++ [1, 0, 0]) ++
        (3 :: rep [2, 0, 4] s) ++ (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [1, 0, 0, 3]) ++
        (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    rw [rep_succ']; simp
  have E6 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [2, 2, 0, 4]) ++
        (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E7 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) := by
    rw [rep_succ]; simp
  have E8 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ]; simp
  have E9 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        ([2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++ [3, 1, 0, 2, 2, 0] ++
        (4 :: (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ']; simp
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        [3, 2, 2, 2, 2, 0] ++
        (4 :: (rep [2, 0, 4] s ++ (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    simp [rep_shift']
  have E11 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) := by
    simp
  have E12 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * m + 4) 2 ++ [0])))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ rep (tokU 1 1) s ++
        tokU 1 (2 * m + 4) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SCD : Win St.A St.A (3 * r + 14) (3 * r + 3 * s + 21) _ _ (3 * s + 7) :=
    HCD.cast (by simp; ring) (by simp; ring) rfl E3 (by ring)
  have SE : Win St.A St.A (3 * r + 3 * s + 21) (3 * r + 3 * s + 17) _ _ (10 * m + 14) :=
    HE.cast (by simp; ring) (by simp; ring) rfl E4 rfl
  have SF : Win St.A St.A (3 * r + 3 * s + 17) (3 * r + 17) _ _ (3 * s) :=
    HF.cast (by simp; ring) (by simp; ring) rfl E5 (by ring)
  have SG : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ 6 :=
    HG.cast (by simp; ring) (by simp; ring) rfl E6 rfl
  have SH : Win St.A St.A (3 * r + 13) 10 _ _ (3 * r + 3) :=
    HH.cast (by simp; ring) (by simp) rfl E7 (by ring)
  have SI : Win St.A St.B 10 11 _ _ 7 :=
    HI.cast (by simp) (by simp) rfl E8 rfl
  have SJ : Win St.B St.B 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HJ.cast (by simp) (by simp; ring) rfl E9 (by ring)
  have SK : Win St.B St.A (3 * r + 14) (3 * r + 11) _ _ 15 :=
    HK.cast (by simp; ring) (by simp; ring) rfl E10 rfl
  have SL : Win St.A St.A (3 * r + 11) 11 _ _ (3 * r) :=
    HL.cast (by simp; ring) (by simp) rfl E11 (by ring)
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
  exact (T10.trans SM (by simp; omega)).cast rfl rfl rfl rfl (by ring)


/-! ### One full turn of the three-phase cycle -/

/-- **One full turn of the three-phase cycle `P1 → P2 → P3 → P1`.**  Starting from the
phase-`P1` shape `U(2,1) U(4,1) · u^(r+1) · U(1,2m+2)` with nine blank cells to the left of
the head, the machine performs the three left-end macro steps `rule_P1_gen`, `rule_P2` and
`rule_P3_U21` — in total exactly `233 + 18r + 30m` steps — and returns to the phase-`P1`
shape, nine cells further left, with the tape now reading
`U(2,1) U(4,1) · U(1,4) · u^r · U(1,2m+8)`.

So one turn of the cycle consumes one token `u`, creates a token `U(1,4)` in its place and
adds six `2`s to the absorbing token.  The head visits nine new cells on the left and never
leaves the displayed window, and the machine does not halt at any of the steps. -/
theorem three_phase_cycle (r m : ℕ) :
    Win St.B St.B 9 0
      ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) r ++ tokU 1 (2 * m + 8) ++ [0])
      (233 + 18 * r + 30 * m) := by
  have H1 := (rule_P1_gen r m).embed (by simp; omega) [0, 0, 0, 0, 0, 0] []
  have H2 := rule_P2.embed (by simp) [0, 0, 0]
    ([4, 2] ++ (tokU 2 1 ++ (rep (tokU 1 1) r ++ (tokU 1 (2 * m + 6) ++ [0]))))
  have H3 := (rule_P3_U21 0 r (m + 2)).embed (by simp; omega) [] []
  have E0 : ([0, 0, 0, 0, 0, 0] ++
        ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
          tokU 1 (2 * m + 2) ++ [0]) ++ [] : List Sym)
      = [0, 0, 0, 0, 0, 0, 0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0] := by
    simp
  have E1 : ([0, 0, 0, 0, 0, 0] ++
        (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
          tokU 1 (2 * m + 6) ++ [0]) ++ [] : List Sym)
      = [0, 0, 0] ++ ([0, 0, 0] ++ tokU 2 2 ++ [0]) ++
        ([4, 2] ++ (tokU 2 1 ++ (rep (tokU 1 1) r ++ (tokU 1 (2 * m + 6) ++ [0])))) := by
    simp [tokU]
  have E2 : ([0, 0, 0] ++ (tokU 2 2 ++ tokV 1 ++ [0]) ++
        ([4, 2] ++ (tokU 2 1 ++ (rep (tokU 1 1) r ++
          (tokU 1 (2 * m + 6) ++ [0])))) : List Sym)
      = [] ++ ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (0 + 1) ++ tokU 2 1 ++
        rep (tokU 1 1) r ++ tokU 1 (2 * (m + 2) + 2) ++ [0]) ++ [] := by
    rw [show 2 * (m + 2) + 2 = 2 * m + 6 from by ring]
    simp [tokU, tokV, rep_succ]
  have E3 : ([] ++ (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) 0 ++ tokU 1 4 ++
        rep (tokU 1 1) r ++ tokU 1 (2 * (m + 2) + 4) ++ [0]) ++ [] : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ tokU 1 4 ++ rep (tokU 1 1) r ++
        tokU 1 (2 * m + 8) ++ [0] := by
    rw [show 2 * (m + 2) + 4 = 2 * m + 8 from by ring]
    simp
  have S1 : Win St.B St.B 9 6 _ _ (91 + 12 * r + 20 * m) :=
    H1.cast (by simp) (by simp) E0 E1 rfl
  have S2 : Win St.B St.B 6 3 _ _ 31 :=
    H2.cast (by simp) (by simp) rfl E2 rfl
  have S3 : Win St.B St.B 3 0 _ _ (111 + 6 * r + 10 * m) :=
    H3.cast (by simp) (by simp) rfl E3 (by ring)
  have C1 := S1.trans S2 (by simp [tokU]; omega)
  exact (C1.trans S3 (by simp [tokU, tokV]; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U21` is being applied. -/
theorem rule_P3_U21_no_halt (r s m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 1 ++
      rep (tokU 1 1) s ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 12 * r + 6 * s + 10 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U21 r s m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
