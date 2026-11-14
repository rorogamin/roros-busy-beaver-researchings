import RequestProject.Carry

/-!
# The `P1` rule with an arbitrary run of `u` tokens

`Cycle.lean` proved the left-end rule `P1` in the case in which the absorbing token
`U(1,2m+2)` comes immediately after the prefix `U(2,1) U(4,1)`, and `Carry.lean` proved
the general form of the rule `P3`.  This file completes the picture by proving the
general form of `P1`: there is a run of `r+1` tokens `u = U(1,1)` between the prefix and
the absorbing token, and

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(1,2m+2) 0
              --(91 + 12r + 20m) steps-->
        U(2,2) u · U(2,1) · u^r · U(1,2m+6) 0
```

Note the difference from `rule_P3_gen`: in the phase `P1` the machine additionally
**raises by one the exponent `a` of the first token after the prefix**.  When that token
is a `u` (which is the case as soon as `r + 1 ≥ 1`) the `u` becomes `U(2,1)` and the carry
of four `2`s travels on to the first token with more than one `2`; when there is no
intervening `u` at all (the case `rule_P1` of `Cycle.lean`) the raise lands on the
absorbing token itself, which is why the two statements have different shapes.

The proof exhibits the computation as twelve macro steps.  Four of them are the parametric
"repeated region" rules — the head crosses the run of `u`s four times (right, left, right,
left) — and two are `cross_back`, the round trip through the run of `2`s in which the four
extra `2`s are deposited.  The remaining six are fixed finite computations discharged by
`decide`.
-/

namespace BB25

/-! ### The six fixed pieces -/

/-- The opening `16` steps: the head leaves the three blank cells, rewrites `U(2,1)` and
crosses the `4`-run of `U(4,1)`, arriving in state `A` on the `0` that begins the first
`u`. -/
theorem p1g_open :
    Win St.B St.A 3 13
      [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0]
      [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] 16 :=
  Win.of_lrun (by decide)

/-- The reflection at the `4`-run of `U(4,1)` (now a run of `0`s): the head, coming back
leftwards, is turned around and starts rightwards again, in state `B`. -/
theorem p1g_reflect : Win St.A St.B 3 3 [0, 0, 0, 3] [1, 3, 1, 4] 8 :=
  Win.of_lrun (by decide)

/-- One step: in state `B` on a `4`, write `0` and move right. -/
theorem p1g_B4 : Win St.B St.B 0 1 [4, 2] [0, 2] 1 := Win.of_lrun (by decide)

/-- The five steps in which the head, back at the left end of the run of `u`s, turns the
last `1 0 3` into the token `U(2,1)`. -/
theorem p1g_back : Win St.A St.B 5 0 [0, 1, 3, 1, 0, 3] [0, 4, 4, 2, 0, 4] 5 :=
  Win.of_lrun (by decide)

/-- The closing `10` steps: the head rebuilds the prefix `U(2,2) u` and stops on the new
leftmost non-blank cell in state `B`. -/
theorem p1g_close :
    Win St.B St.B 8 0
      [0, 1, 3, 1, 0, 0, 3, 1, 0]
      [0, 4, 4, 2, 2, 0, 4, 2, 0] 10 :=
  Win.of_lrun (by decide)

/-! ### The rule -/

/-- **The general `P1` rule.**  The head is in state `B` on the leftmost non-blank cell,
with three blank cells to its left, and the tape reads
`U(2,1) U(4,1) · U(1,1)^(r+1) · U(1,2m+2)` followed by the `0` of the next token.  In
exactly `91 + 12r + 20m` steps the machine raises the first `u` to `U(2,1)`, delivers a
carry of four `2`s through the remaining `r` tokens `u` into `U(1,2m+2)`, and arrives,
again in state `B`, on the new leftmost non-blank cell three cells further left, the tape
now reading `U(2,2) U(1,1) · U(2,1) · U(1,1)^r · U(1,2m+6)`.  Nothing outside the window is
read or written, so the rest of the tape is arbitrary and untouched. -/
theorem rule_P1_gen (r m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++ tokU 1 (2 * m + 6) ++ [0])
      (91 + 12 * r + 20 * m) := by
  -- splitting off leading `2`s from the runs of `2`s
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  have q4 : List.replicate (2 * m + 4) (2 : Sym) = 2 :: List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  have q3 : List.replicate (2 * m + 3) (2 : Sym) = 2 :: List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  -- stage A : the opening
  have HA := p1g_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage B : the carry crosses the `u`s rightwards
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 2)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] (List.replicate (2 * m) 2 ++ [0])
  -- stage C : it crosses the run of `2`s and comes back
  have HC := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) []
  -- stage D : it crosses the `u`s leftwards
  have HD := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage E : the reflection at the `4`-run of `U(4,1)`
  have HE := p1g_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++ [0]))
  -- stage F : one step to the right
  have HF := p1g_B4.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage G : the second rightward crossing of the `u`s
  have HG := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] (List.replicate (2 * m + 3) 2 ++ [0])
  -- stage H : one step to the right
  have HH := carry_B2.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1))
    (List.replicate (2 * m + 2) 2 ++ [0])
  -- stage I : the second crossing of the run of `2`s
  have HI := (cross_back (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r) []
  -- stage J : the second leftward crossing of the `u`s
  have HJ := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] (List.replicate (2 * m + 6) 2 ++ [0])
  -- stage K : the last `u` becomes `U(2,1)`
  have HK := p1g_back.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1]
    (rep [2, 0, 4] r ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage L : the closing
  have HL := p1g_close.embed (by simp) []
    ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 6) 2 ++ [0])))
  -- the thirteen tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++
          (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [0, 4, 2] (r + 2) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [rep_succ, rep_succ', q2]; simp
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] (r + 2) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ', rep_succ', q1]; simp
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [rep_succ']; simp
  have E4 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3] ++
        (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++ [0])) := by
    simp
  have E5 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 3, 1, 4] ++
        (rep [2, 0, 4] (r + 1) ++ (List.replicate (2 * m + 4) 2 ++ [0])) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [4, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ]; simp
  have E6 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++
          (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) := by
    rw [rep_succ, q4]; simp
  have E7 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++ [2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [q3]; simp
  have E8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++ [3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ', show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, q3]; simp
  have E9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        (3 :: (List.replicate (2 * (m + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    rw [show 2 * (m + 1) + 4 = 2 * m + 6 from by ring]
    simp [rep_shift']
  have E10 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp
  have E11 : ([0, 1, 3, 1, 0, 0, 3, 1] ++ [0, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0] ++
        ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          (List.replicate (2 * m + 6) 2 ++ [0]))) := by
    simp
  have E12 : ([] ++ [0, 4, 4, 2, 2, 0, 4, 2, 0] ++
        ([4, 4, 2, 0, 4] ++ (rep [2, 0, 4] r ++
          (List.replicate (2 * m + 6) 2 ++ [0]))) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) r ++
        tokU 1 (2 * m + 6) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 13 _ _ 16 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 13 (3 * r + 19) _ _ (3 * r + 6) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC : Win St.A St.A (3 * r + 19) (3 * r + 15) _ _ (10 * m + 14) :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 rfl
  have SD : Win St.A St.A (3 * r + 15) 12 _ _ (3 * r + 3) :=
    HD.cast (by simp; ring) (by simp) rfl E4 (by ring)
  have SE : Win St.A St.B 12 12 _ _ 8 :=
    HE.cast (by simp) (by simp) rfl E5 rfl
  have SF : Win St.B St.B 12 13 _ _ 1 :=
    HF.cast (by simp) (by simp) rfl E6 rfl
  have SG : Win St.B St.B 13 (3 * r + 16) _ _ (3 * r + 3) :=
    HG.cast (by simp) (by simp; ring) rfl E7 (by ring)
  have SH : Win St.B St.A (3 * r + 16) (3 * r + 17) _ _ 1 :=
    HH.cast (by simp; ring) (by simp; ring) rfl E8 rfl
  have SI : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ (10 * m + 24) :=
    HI.cast (by simp; ring) (by simp; ring) rfl E9 (by ring)
  have SJ : Win St.A St.A (3 * r + 13) 13 _ _ (3 * r) :=
    HJ.cast (by simp; ring) (by simp) rfl E10 (by ring)
  have SK : Win St.A St.B 13 8 _ _ 5 :=
    HK.cast (by simp) (by simp) rfl E11 rfl
  have SL : Win St.B St.B 8 0 _ _ 10 :=
    HL.cast (by simp) (by simp) rfl E12 rfl
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
  exact (T10.trans SL (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P1_gen` is being applied. -/
theorem rule_P1_gen_no_halt (r m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 12 * r + 20 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1_gen r m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
