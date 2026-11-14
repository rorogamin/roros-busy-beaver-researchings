import RequestProject.Carry

/-!
# The carry running off the blank right end

Every macro rule proved so far ends with the carry being *absorbed* by a token to the
right.  One row of the carry table of `ANALYSIS.md` §25 is different: when there is no
absorbing token, the carry runs into the blank tape at the right end, bounces there twice
and comes back having created new tokens `u = U(1,1)`.

This row matters twice over.  It is what the machine does at the very beginning, when the
tape is still short; and — because a swept `4`-run is a piece of virtual blank tape and an
infinite run of `u`s is the virtual blank tape on the right (`Fractal.lean`,
`ANALYSIS.md` §24) — it is also what the machine does *inside* every fractal copy of its
own computation.

The two rules proved here are the `P3` and the `P1` case, for an arbitrary number `N` of
tokens `u` between the prefix and the blank:

```
rule_P3_blank : 0 0 0 · U(2,2) V(1) · u^(N+1) · 0 0 0   →   U(2,1) U(4,1) · u^(N+2) · 0
                in exactly 59 + 12N steps
rule_P1_blank : 0 0 0 · U(2,1) U(4,1) · u^N · 0 0 0     →   U(2,2) u · U(2,1) · u^(N+1) · 0
                in exactly 47 + 12N steps
```

Both are `Win` rules, so each also certifies that the head never leaves the displayed
window — in particular it never reads more than three blank cells on the right — and that
the machine does not halt during the steps it covers.

The anatomy is the same in both cases and is the two-pass anatomy of `ANALYSIS.md` §29
with the run of `2`s replaced by the blank: the head crosses the run of `u`s rightwards,
turns around on the blank in three steps (writing one `2`), sweeps back, turns the corner,
crosses the run again, turns around on the blank a second time and comes back to the left
end.  Each of the two bounces converts two blank cells into the tail of a fresh token `u`,
which is why the run of `u`s grows by one and why the step count grows by `12` per `u`
(four crossings of three cells each).
-/

namespace BB25

/-! ### The three fixed pieces of the `P3` rule -/

/-- **The turn-around on the blank tape.**  In state `A` on the first blank cell after a
swept block (so with a `3` to its left), the head writes a `1`, steps onto the next blank
cell, comes back and overwrites the `1` with a `2`; three steps later it is back on the
`3`, in state `A`, and one blank cell has become the `2` that ends a fresh token. -/
theorem blank_turn : Win St.A St.A 1 0 [3, 0, 0] [3, 2, 0] 3 :=
  Win.of_lrun (by decide)

/-- Two steps at the left end of the swept region: the head turns the corner and starts
its second rightward pass. -/
theorem p3b_two : Win St.A St.A 0 2 [0, 2, 0] [1, 3, 0] 2 :=
  Win.of_lrun (by decide)

/-- The closing eight steps of the `P3` rule: the head rebuilds the prefix
`U(2,1) U(4,1)` and stops on the new leftmost non-blank cell in state `B`. -/
theorem p3b_close :
    Win St.A St.B 8 0
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 2] [0, 4, 4, 2, 0, 4, 4, 4, 4, 2] 8 :=
  Win.of_lrun (by decide)

/-! ### Two shifting identities for runs of blocks -/

/-- `[0,4] ++ (2 0 4)^k ++ [2] = (0 4 2)^(k+1)`: the same run of blocks read one token
further to the left. -/
lemma shift_204_042 (k : ℕ) :
    ([0, 4] ++ (rep [2, 0, 4] k ++ [2]) : List Sym) = rep [0, 4, 2] (k + 1) := by
  have h1 : ((4 : Sym) :: (rep [2, 0, 4] k ++ [2]) : List Sym)
      = rep [4, 2, 0] k ++ [4, 2] := by
    simpa using rep_shift' 4 2 0 k [2]
  have h2 : ((0 : Sym) :: (rep [4, 2, 0] k ++ [4, 2]) : List Sym)
      = rep [0, 4, 2] k ++ [0, 4, 2] := by
    simpa using rep_shift' 0 4 2 k [4, 2]
  calc ([0, 4] ++ (rep [2, 0, 4] k ++ [2]) : List Sym)
      = (0 : Sym) :: ((4 : Sym) :: (rep [2, 0, 4] k ++ [2])) := by simp
    _ = (0 : Sym) :: (rep [4, 2, 0] k ++ [4, 2]) := by rw [h1]
    _ = rep [0, 4, 2] k ++ [0, 4, 2] := h2
    _ = rep [0, 4, 2] (k + 1) := (rep_succ' (w := [0, 4, 2]) k).symm

/-- The same identity with an extra cell on the right. -/
lemma shift_204_042' (k : ℕ) (t : List Sym) :
    ([0, 4] ++ (rep [2, 0, 4] k ++ ([2] ++ t))) = rep [0, 4, 2] (k + 1) ++ t := by
  have := shift_204_042 k
  calc ([0, 4] ++ (rep [2, 0, 4] k ++ ([2] ++ t)))
      = ([0, 4] ++ (rep [2, 0, 4] k ++ [2])) ++ t := by simp [List.append_assoc]
    _ = rep [0, 4, 2] (k + 1) ++ t := by rw [this]

/-! ### The `P3` rule -/

/-- **The `P3` rule with a blank right end.**  The head is in state `B` on the leftmost
non-blank cell, with three blank cells to its left, and the tape reads
`U(2,2) V(1) · u^(N+1)` followed by blank.  In exactly `59 + 12N` steps the machine
bounces twice off the blank, turning it into two fresh tokens `u`, and arrives again in
state `B` on the new leftmost non-blank cell three cells further left, the tape now
reading `U(2,1) U(4,1) · u^(N+2)`. -/
theorem rule_P3_blank (N : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (N + 1) ++ [0, 0, 0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (N + 2) ++ [0])
      (59 + 12 * N) := by
  -- stage A : the opening
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] N ++ [0, 0, 0]))
  -- stage B : the carry crosses the `u`s rightwards
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (N + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] [0, 0]
  -- stage C : the first bounce off the blank
  have HC := blank_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) [0]
  -- stage D : the leftward sweep back
  have HD := (Win.of_sweepL (sweepL_bulk (N + 2)) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1] [2, 0, 0]
  -- stage E : turning the corner
  have HE := p3b_two.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0, 0]))
  -- stage F : the second rightward crossing
  have HF := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (N + 2)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3] [0]
  -- stage G : the second bounce off the blank
  have HG := blank_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [1, 0, 3] (N + 1) ++ [1, 0])) []
  -- stage H : the second leftward sweep
  have HH := (Win.of_sweepL (sweepL_bulk (N + 2)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1] [2, 0]
  -- stage I : the closing
  have HI := p3b_close.embed (by simp) []
    ([0, 4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0]))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (N + 1) ++ [0, 0, 0]
        : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] N ++ [0, 0, 0])) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] N ++ [0, 0, 0])) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (N + 1) ++ [0]) ++ [0, 0] := by
    rw [rep_succ]; simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (N + 1) ++ [0]) ++ [0, 0]
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) ++ [3, 0, 0] ++
        [0] := by
    rw [rep_succ' (w := [1, 0, 3]) N]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) ++
        [3, 2, 0] ++ [0] : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ ((0 : Sym) :: rep [1, 0, 3] (N + 2)) ++ [2, 0, 0] := by
    rw [show (N + 2) = (N + 1) + 1 from rfl, rep_succ' (w := [1, 0, 3]) (N + 1),
      rep_succ (w := [1, 0, 3]) N]
    simp
  have E4 : ([0, 1, 3, 1, 0, 1, 1] ++ ((0 : Sym) :: rep [2, 0, 4] (N + 2)) ++ [2, 0, 0]
        : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0, 0])) := by
    rw [rep_succ (w := [2, 0, 4]) (N + 1)]; simp
  have E5 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 0] ++
        ([4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0, 0])) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [0, 4, 2] (N + 2) ++ [0]) ++ [0] := by
    have h := shift_204_042' (N + 1) [0, 0]
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h ⊢
    rw [h]
  have E6 : ([0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [1, 0, 3] (N + 2) ++ [0]) ++ [0]
        : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [1, 0, 3] (N + 1) ++ [1, 0])) ++ [3, 0, 0] ++
        [] := by
    rw [rep_succ' (w := [1, 0, 3]) (N + 1)]; simp
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 1, 3] ++ (rep [1, 0, 3] (N + 1) ++ [1, 0])) ++
        [3, 2, 0] ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1] ++ ((3 : Sym) :: rep [1, 0, 3] (N + 2)) ++ [2, 0] := by
    rw [show (N + 2) = (N + 1) + 1 from rfl, rep_succ' (w := [1, 0, 3]) (N + 1)]
    simp
  have E8 : ([0, 1, 3, 1, 0, 1, 1, 1] ++ ((3 : Sym) :: rep [2, 0, 4] (N + 2)) ++ [2, 0]
        : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0])) := by
    rw [rep_succ (w := [2, 0, 4]) (N + 1)]; simp
  have E9 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] (N + 1) ++ [2, 0])) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) (N + 2) ++ [0] := by
    have h := shift_204_042' (N + 1) [0]
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h ⊢
    rw [h, show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU]
  -- chain the nine stages
  have SA : Win St.B St.A 3 11 _ _ 22 := HA.cast (by simp +arith) (by simp +arith) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * N + 14) _ _ (3 * N + 3) :=
    HB.cast (by simp +arith) (by simp +arith) rfl E2 (by simp +arith)
  have SC : Win St.A St.A (3 * N + 14) (3 * N + 13) _ _ 3 :=
    HC.cast (by simp +arith) (by simp +arith) rfl E3 rfl
  have SD : Win St.A St.A (3 * N + 13) 7 _ _ (3 * N + 6) :=
    HD.cast (by simp +arith) (by simp +arith) rfl E4 (by simp +arith)
  have SE : Win St.A St.A 7 9 _ _ 2 := HE.cast (by simp +arith) (by simp +arith) rfl E5 rfl
  have SF : Win St.A St.A 9 (3 * N + 15) _ _ (3 * N + 6) :=
    HF.cast (by simp +arith) (by simp +arith) rfl E6 (by simp +arith)
  have SG : Win St.A St.A (3 * N + 15) (3 * N + 14) _ _ 3 :=
    HG.cast (by simp +arith) (by simp +arith) rfl E7 rfl
  have SH : Win St.A St.A (3 * N + 14) 8 _ _ (3 * N + 6) :=
    HH.cast (by simp +arith) (by simp +arith) rfl E8 (by simp +arith)
  have SI : Win St.A St.B 8 0 _ _ 8 := HI.cast (by simp +arith) (by simp +arith) rfl E9 rfl
  have U1 := SA.trans SB (by simp +arith)
  have U2 := U1.trans SC (by simp +arith)
  have U3 := U2.trans SD (by simp +arith)
  have U4 := U3.trans SE (by simp +arith)
  have U5 := U4.trans SF (by simp +arith)
  have U6 := U5.trans SG (by simp +arith)
  have U7 := U6.trans SH (by simp +arith)
  exact (U7.trans SI (by simp +arith)).cast rfl rfl rfl rfl (by ring)

/-- The `P3` blank-end rule certifies that the machine does not halt during the
`59 + 12N` steps it covers. -/
theorem rule_P3_blank_no_halt (N : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (N + 1) ++ [0, 0, 0])) :
    ∀ m ≤ 59 + 12 * N, ¬ Halted (step^[m] ⟨St.B, a + (3 : ℕ), T⟩) :=
  (rule_P3_blank N).no_halt (fun h => St.noConfusion h) T a hs

/-! ### The three fixed pieces of the `P1` rule -/

/-- The opening `16` steps of the `P1` rule: the head leaves the three blank cells,
rewrites the prefix `U(2,1) U(4,1)` and arrives, in state `A`, at the `0` that begins the
run of tokens `u`. -/
theorem p1b_open :
    Win St.B St.A 3 13
      [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0]
      [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] 16 :=
  Win.of_lrun (by decide)

/-- The reflection at the swept `4`-run of `U(4,1)`: the head, coming back leftwards, is
turned around inside the run of `0`s and starts rightwards again. -/
theorem p1b_reflect : Win St.A St.A 3 2 [0, 0, 0, 3, 2] [1, 3, 0, 4, 2] 7 :=
  Win.of_lrun (by decide)

/-- The closing `12` steps of the `P1` rule: the head rebuilds the prefix
`U(2,2) u U(2,1)` and stops on the new leftmost non-blank cell in state `B`. -/
theorem p1b_close :
    Win St.A St.B 10 0
      [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 2] [0, 4, 4, 2, 2, 0, 4, 2, 0, 4, 4, 2] 12 :=
  Win.of_lrun (by decide)

/-! ### The `P1` rule -/

/-- **The `P1` rule with a blank right end.**  The head is in state `B` on the leftmost
non-blank cell, with three blank cells to its left, and the tape reads
`U(2,1) U(4,1) · u^N` followed by blank.  In exactly `47 + 12N` steps the machine bounces
twice off the blank, turning it into a fresh token `u`, and arrives again in state `B` on
the new leftmost non-blank cell three cells further left, the tape now reading
`U(2,2) u · U(2,1) · u^(N+1)`. -/
theorem rule_P1_blank (N : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) N ++ [0, 0, 0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (N + 1) ++ [0])
      (47 + 12 * N) := by
  -- stage A : the opening
  have HA := p1b_open.embed (by simp) [] (rep [4, 2, 0] N ++ [0, 0])
  -- stage B : the carry crosses the `u`s rightwards
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) N) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] [0, 0]
  -- stage C : the first bounce off the blank
  have HC := blank_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ rep [3, 1, 0] N) [0]
  -- stage D : the leftward sweep back
  have HD := (Win.of_sweepL (sweepL_bulk N) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] [2, 0, 0]
  -- stage E : the reflection at the `4`-run of `U(4,1)`
  have HE := p1b_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    (rep [0, 4, 2] N ++ [0, 0])
  -- stage F : the second rightward crossing
  have HF := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (N + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] [0]
  -- stage G : the second bounce off the blank
  have HG := blank_turn.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) []
  -- stage H : the second leftward sweep
  have HH := (Win.of_sweepL (sweepL_bulk (N + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] [2, 0]
  -- stage I : the closing
  have HI := p1b_close.embed (by simp) [] (rep [0, 4, 2] (N + 1) ++ [0])
  -- the tape words the computation passes through
  have sh0 : ∀ (t : List Sym), ((0 : Sym) :: (rep [4, 2, 0] N ++ t) : List Sym)
      = rep [0, 4, 2] N ++ ((0 : Sym) :: t) := fun t => rep_shift' 0 4 2 N t
  have sh3 : ∀ (k : ℕ) (t : List Sym), ((3 : Sym) :: (rep [1, 0, 3] k ++ t) : List Sym)
      = rep [3, 1, 0] k ++ ((3 : Sym) :: t) := fun k t => rep_shift' 3 1 0 k t
  have sh2 : ∀ (k : ℕ) (t : List Sym), ((2 : Sym) :: (rep [0, 4, 2] k ++ t) : List Sym)
      = rep [2, 0, 4] k ++ ((2 : Sym) :: t) := fun k t => rep_shift' 2 0 4 k t
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) N ++ [0, 0, 0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++ (rep [4, 2, 0] N ++ [0, 0]) := by
    have h := sh0 [0, 0]
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp only [List.cons_append, List.nil_append, List.append_assoc, tokU] at h ⊢
    rw [h]
    simp
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        (rep [4, 2, 0] N ++ [0, 0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [0, 4, 2] N ++ [0]) ++ [0, 0] := by
    have h := sh0 [0, 0]
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h ⊢
    rw [h]
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ (rep [1, 0, 3] N ++ [0]) ++ [0, 0]
        : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ rep [3, 1, 0] N) ++ [3, 0, 0] ++ [0] := by
    have h := sh3 N [0, 0, 0]
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h ⊢
    rw [h]
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ rep [3, 1, 0] N) ++ [3, 2, 0] ++ [0]
        : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [1, 0, 3] N) ++
        [2, 0, 0] := by
    have h := sh3 N [2, 0, 0]
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h ⊢
    rw [h]
  have E4 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++ ((3 : Sym) :: rep [2, 0, 4] N) ++
        [2, 0, 0] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3, 2] ++ (rep [0, 4, 2] N ++ [0, 0]) := by
    have h := sh2 N [0, 0]
    simp only [List.cons_append, List.nil_append] at h ⊢
    rw [h]
  have E5 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 3, 0, 4, 2] ++
        (rep [0, 4, 2] N ++ [0, 0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++ (rep [0, 4, 2] (N + 1) ++ [0]) ++ [0] := by
    rw [rep_succ]; simp
  have E6 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++ (rep [1, 0, 3] (N + 1) ++ [0]) ++ [0]
        : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) ++ [3, 0, 0] ++
        [] := by
    rw [rep_succ' (w := [1, 0, 3]) N]; simp
  have E7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++ (rep [1, 0, 3] N ++ [1, 0])) ++
        [3, 2, 0] ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ ((3 : Sym) :: rep [1, 0, 3] (N + 1)) ++
        [2, 0] := by
    rw [rep_succ' (w := [1, 0, 3]) N]; simp
  have E8 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++ ((3 : Sym) :: rep [2, 0, 4] (N + 1)) ++
        [2, 0] : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 2] ++ (rep [0, 4, 2] (N + 1) ++ [0]) := by
    have h := sh2 (N + 1) [0]
    simp only [List.cons_append, List.nil_append] at h ⊢
    rw [h]
  have E9 : ([] ++ [0, 4, 4, 2, 2, 0, 4, 2, 0, 4, 4, 2] ++
        (rep [0, 4, 2] (N + 1) ++ [0]) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 1 ++ rep (tokU 1 1) (N + 1) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU]
  -- chain the nine stages
  have SA : Win St.B St.A 3 13 _ _ 16 :=
    HA.cast (by simp +arith) (by simp +arith) E0.symm E1 rfl
  have SB : Win St.A St.A 13 (3 * N + 13) _ _ (3 * N) :=
    HB.cast (by simp +arith) (by simp +arith) rfl E2
      (by simp +arith)
  have SC : Win St.A St.A (3 * N + 13) (3 * N + 12) _ _ 3 :=
    HC.cast (by simp +arith) (by simp +arith) rfl E3 rfl
  have SD : Win St.A St.A (3 * N + 12) 12 _ _ (3 * N) :=
    HD.cast (by simp +arith) (by simp +arith) rfl E4
      (by simp +arith)
  have SE : Win St.A St.A 12 11 _ _ 7 :=
    HE.cast (by simp +arith) (by simp +arith) rfl E5 rfl
  have SF : Win St.A St.A 11 (3 * N + 14) _ _ (3 * N + 3) :=
    HF.cast (by simp +arith) (by simp +arith) rfl E6
      (by simp +arith)
  have SG : Win St.A St.A (3 * N + 14) (3 * N + 13) _ _ 3 :=
    HG.cast (by simp +arith) (by simp +arith) rfl E7 rfl
  have SH : Win St.A St.A (3 * N + 13) 10 _ _ (3 * N + 3) :=
    HH.cast (by simp +arith) (by simp +arith) rfl E8
      (by simp +arith)
  have SI : Win St.A St.B 10 0 _ _ 12 :=
    HI.cast (by simp +arith) (by simp +arith) rfl E9 rfl
  have U1 := SA.trans SB (by simp +arith)
  have U2 := U1.trans SC (by simp +arith)
  have U3 := U2.trans SD (by simp +arith)
  have U4 := U3.trans SE (by simp +arith)
  have U5 := U4.trans SF (by simp +arith)
  have U6 := U5.trans SG (by simp +arith)
  have U7 := U6.trans SH (by simp +arith)
  exact (U7.trans SI (by simp +arith)).cast rfl rfl rfl rfl (by ring)

/-- The `P1` blank-end rule certifies that the machine does not halt during the
`47 + 12N` steps it covers. -/
theorem rule_P1_blank_no_halt (N : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) N ++ [0, 0, 0])) :
    ∀ m ≤ 47 + 12 * N, ¬ Halted (step^[m] ⟨St.B, a + (3 : ℕ), T⟩) :=
  (rule_P1_blank N).no_halt (fun h => St.noConfusion h) T a hs

end BB25
