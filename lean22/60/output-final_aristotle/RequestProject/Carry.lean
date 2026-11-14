import RequestProject.Cycle

/-!
# The carry crossing an arbitrary run of `u` tokens

`Cycle.lean` proved the left-end rule `P3` in the case in which the absorbing token
`U(1,2m)` comes immediately after the prefix.  In general there is a run of `r` tokens
`u = U(1,1)` in between, and the carry simply passes through them.  This file proves the
rule for every `r`:

```
0 0 0 · U(2,2) V(1) U(1,1) · u^r · U(1,2m+2) 0
              --(91 + 12r + 20m) steps-->
        U(2,1) U(4,1) · u^r · U(1,2m+6) 0
```

The proof exhibits the computation as nine macro steps.  Four of them are the parametric
"repeated region" rules: the head crosses the run of `u`s **four** times (right, left,
right, left), and each crossing is a run rule of `Words.lean`/`Chains.lean`
(`sweepR_042`, `sweepL_103`, `sweepR_204`, `sweepL_310` iterated).  In between it crosses
the run of `2`s twice, which is `cross_back`.  The remaining five steps are fixed finite
computations discharged by `decide`.

This is the longitudinal picture in its clearest form: one macro step advances every
`u`-block of the bulk by two of the six phases of the cell cycle
`0 4 2 → 1 0 3 → 2 0 4 → 3 1 0 → 4 2 0 → 0 3 1 → 0 4 2`, and pushes four extra `2`s into
the first block that has more than one `2`.
-/

namespace BB25

/-! ### Shifting the window of a periodic run -/

/-- Shifting the window of a `3`-periodic run by one cell. -/
lemma rep_shift (a b c : Sym) (r : ℕ) : a :: rep [b, c, a] r = rep [a, b, c] r ++ [a] := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [rep_succ, rep_succ]
      show [a, b, c] ++ (a :: rep [b, c, a] r) = [a, b, c] ++ rep [a, b, c] r ++ [a]
      rw [ih, List.append_assoc]

/-- `rep_shift` in the form in which it is used below. -/
lemma rep_shift' (a b c : Sym) (r : ℕ) (t : List Sym) :
    a :: (rep [b, c, a] r ++ t) = rep [a, b, c] r ++ (a :: t) := by
  rw [← List.cons_append, rep_shift, List.append_assoc]
  rfl

/-! ### The five fixed pieces -/

/-- The opening `22` steps: the head leaves the three blank cells, rewrites the prefix
`U(2,2) V(1)` and arrives, in state `A`, at the `0` that begins the first `u`. -/
theorem carry_open :
    Win St.B St.A 3 11
      [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0]
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] 22 :=
  Win.of_lrun (by decide)

/-- The reflection at the `4`-run of `U(4,1)`: the head, coming back leftwards, is turned
around and starts rightwards again, now in state `B`. -/
theorem carry_reflect : Win St.A St.B 3 4 [0, 1, 0, 3, 2] [1, 3, 1, 0, 2] 7 :=
  Win.of_lrun (by decide)

/-- One step: in state `B` on a `2`, write `3` and move right. -/
theorem carry_B2 : Win St.B St.A 0 1 [2, 2] [3, 2] 1 := Win.of_lrun (by decide)

/-- One step: in state `A` on a `3`, write `4` and move left. -/
theorem carry_A3 : Win St.A St.B 1 0 [0, 3] [0, 4] 1 := Win.of_lrun (by decide)

/-- The closing `10` steps: the head rebuilds the prefix `U(2,1) U(4,1)` and stops on the
new leftmost non-blank cell in state `B`. -/
theorem carry_close :
    Win St.B St.B 10 0
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
      [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] 10 :=
  Win.of_lrun (by decide)

/-! ### The rule -/

/-- **The general `P3` rule.**  The head is in state `B` on the leftmost non-blank cell,
with three blank cells to its left, and the tape reads
`U(2,2) V(1) U(1,1) · U(1,1)^r · U(1,2m+2)` followed by the `0` of the next token.  In
exactly `91 + 12r + 20m` steps the machine delivers a carry of four `2`s through the `r`
intervening `u` tokens into `U(1,2m+2)` and arrives, again in state `B`, on the new
leftmost non-blank cell three cells further left, the tape now reading
`U(2,1) U(4,1) · U(1,1)^r · U(1,2m+6)`.  Nothing outside the window is read or written,
so the rest of the tape is arbitrary and untouched. -/
theorem rule_P3_gen (r m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 (2 * m + 6) ++ [0])
      (91 + 12 * r + 20 * m) := by
  -- splitting off leading `2`s from the run of `2`s
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have q1 : List.replicate (2 * m + 1) (2 : Sym) = 2 :: List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  have q4 : List.replicate (2 * m + 4) (2 : Sym) = 2 :: List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  have q3 : List.replicate (2 * m + 3) (2 : Sym) = 2 :: List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  -- stage A : the opening
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0]))))
  -- stage B : the carry crosses the `u`s rightwards
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 2)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] (List.replicate (2 * m) 2 ++ [0])
  -- stage C : it crosses the run of `2`s and comes back
  have HC := (cross_back m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) []
  -- stage D : it crosses the `u`s leftwards
  have HD := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] (List.replicate (2 * m + 4) 2 ++ [0])
  -- stage E : the reflection at the `4`-run of `U(4,1)`
  have HE := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 4) 2 ++ [0])))
  -- stage F : the second rightward crossing of the `u`s
  have HF := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] (List.replicate (2 * m + 3) 2 ++ [0])
  have HF2 := carry_B2.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1))
    (List.replicate (2 * m + 2) 2 ++ [0])
  -- stage G : the second crossing of the run of `2`s
  have HG := (cross_back (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) []
  -- stage H : the second leftward crossing of the `u`s
  have HH1 := carry_A3.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ++ rep [0, 3, 1] r)
    (List.replicate (2 * m + 6) 2 ++ [0])
  have HH2 := (Win.of_sweepL (sweepL_rep sweepL_310 (by simp) r) 0).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))
  -- stage I : the closing
  have HI := carry_close.embed (by simp) []
    (rep [4, 2, 0] r ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
  -- the eleven tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 1 (2 * m + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4] ++ (List.replicate (2 * m + 2) 2 ++ [0])))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 2) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) := by
    rw [rep_succ, rep_succ', q2]; simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 2) ++ [2]) ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ', rep_succ', q1]; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] r ++ [1, 0])) ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) := by
    rw [rep_succ']; simp
  have E4 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        (List.replicate (2 * m + 4) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 4) 2 ++ [0]))) := by
    rw [rep_succ]; simp
  have E5 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ (List.replicate (2 * m + 4) 2 ++ [0]))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) := by
    rw [rep_succ, q4]; simp
  have E6 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        (List.replicate (2 * m + 3) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++ [2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) := by
    rw [q3]; simp
  have E7 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] (r + 1)) ++ [3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 3) 2 ++ [0])) ++ [] := by
    rw [rep_succ', q3]; simp
  have E8 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        (3 :: (List.replicate (2 * m + 6) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ++ rep [0, 3, 1] r) ++ [0, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp [rep_shift']
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ++ rep [0, 3, 1] r) ++ [0, 4] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ++ (0 :: rep [3, 1, 0] r) ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) := by
    simp [rep_shift']
  have E10 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1] ++ (0 :: rep [4, 2, 0] r) ++
        ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        (rep [4, 2, 0] r ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) := by
    simp
  have E11 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        (rep [4, 2, 0] r ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 (2 * m + 6) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * r + 17) _ _ (3 * r + 6) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ (10 * m + 14) :=
    HC.cast (by simp; ring) (by simp; ring) rfl E3 rfl
  have SD : Win St.A St.A (3 * r + 13) 10 _ _ (3 * r + 3) :=
    HD.cast (by simp; ring) (by simp) rfl E4 (by ring)
  have SE : Win St.A St.B 10 11 _ _ 7 :=
    HE.cast (by simp) (by simp) rfl E5 rfl
  have SF : Win St.B St.B 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HF.cast (by simp) (by simp; ring) rfl E6 (by ring)
  have SF2 : Win St.B St.A (3 * r + 14) (3 * r + 15) _ _ 1 :=
    HF2.cast (by simp; ring) (by simp; ring) rfl E7 rfl
  have SG : Win St.A St.A (3 * r + 15) (3 * r + 11) _ _ (10 * m + 24) :=
    HG.cast (by simp; ring) (by simp; ring) rfl E8 (by ring)
  have SH1 : Win St.A St.B (3 * r + 11) (3 * r + 10) _ _ 1 :=
    HH1.cast (by simp; ring) (by simp; ring) rfl E9 rfl
  have SH2 : Win St.B St.B (3 * r + 10) 10 _ _ (3 * r) :=
    HH2.cast (by simp; ring) (by simp) rfl E10 (by ring)
  have SI : Win St.B St.B 10 0 _ _ 10 :=
    HI.cast (by simp) (by simp) rfl E11 rfl
  have T1 := SA.trans SB (by simp; omega)
  have T2 := T1.trans SC (by simp; omega)
  have T3 := T2.trans SD (by simp; omega)
  have T4 := T3.trans SE (by simp; omega)
  have T5 := T4.trans SF (by simp; omega)
  have T6 := T5.trans SF2 (by simp; omega)
  have T7 := T6.trans SG (by simp; omega)
  have T8 := T7.trans SH1 (by simp; omega)
  have T9 := T8.trans SH2 (by simp; omega)
  exact (T9.trans SI (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_gen` is being applied. -/
theorem rule_P3_gen_no_halt (r m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 12 * r + 20 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_gen r m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

/-! ### The unfolding of a compressed token, in two instances

Simulation (`sim/fractal.py`) says that when the carry reaches a token `U(3j+1,1)` that
token unfolds into a copy of the tape at the `j`-th `B`-event.  The two smallest instances
are local rules, so they can be checked outright.  In both the machine starts in state `B`
on the leftmost non-blank cell with three blank cells to its left, and stops in state `B`
on the new leftmost non-blank cell three cells further left. -/

set_option maxRecDepth 20000 in
/-- `U(4,1)` unfolds into `U(1,1) U(1,2)` — a copy of `W₁ = U(2,2) U(1,1)`, whose `core`
is empty and whose prefix for the phase `P2`/`P3` is `U(1,1) U(1,2)`. -/
theorem unfold_U4 :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 4 1 ++ tokU 1 2 ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 2 ++ tokV 5 ++ [0]) 157 :=
  Win.of_lrun (by decide)

set_option maxRecDepth 40000 in
/-- `U(10,1)` unfolds into `U(1,1) U(1,1) U(4,1)` — a copy of `W₃ = U(2,1) U(4,1) U(1,1)²`,
whose `core` is `U(4,1)` and whose prefix for the phase `P1` is `U(1,1) U(1,1)`; the carry
that passes on has grown from `4` to `10`. -/
theorem unfold_U10 :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 10 1 ++ tokU 1 1 ++ tokU 1 1 ++
        tokU 1 2 ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 4 1 ++ tokU 1 12 ++ [0]) 379 :=
  Win.of_lrun (by decide)

end BB25
