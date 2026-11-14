import RequestProject.LeftRules

/-!
# The three-phase cycle at the left end

`LeftRules.lean` proved the first of the three left-end macro rules, `rule_P2`.  This file
proves the other two, in the case in which the token following the prefix is `U(1,2m)`
with `m ≥ 1`:

```
P1 :  0 0 0 · U(2,1) U(4,1)     U(1,2m) 0  --(59+20m) steps-->  U(2,2) U(1,1) U(2,2m+4) 0
P3 :  0 0 0 · U(2,2) V(1) U(1,1) U(1,2m) 0 --(71+20m) steps-->  U(2,1) U(4,1) U(1,2m+4) 0
```

(in the formal statements `m` is replaced by `m+1`, so that `m ≥ 1` is automatic).

Both are *window* rules in the sense of `Local.lean`: the head provably never leaves the
displayed window, so the rest of the tape is arbitrary and is not touched, and in
particular the machine does not halt while the rule is being applied.

Each rule is assembled from five pieces.  Four of the five are fixed finite computations,
discharged by `decide`; the fifth, `cross_back`, is the parametric "repeated region" of
the longitudinal analysis: a marker `1 0 3` sitting immediately to the left of a run of
`2n+1` twos crosses the run and comes back, leaving a run of `2n+4` twos behind, in
exactly `10n+14` steps.
-/

namespace BB25

/-! ### A convenience: rewriting the parameters of a window rule -/

theorem Win.cast {q q' : St} {k k' : ℕ} {l l' : List Sym} {n : ℕ}
    (h : Win q q' k k' l l' n) {k2 k2' : ℕ} {l2 l2' : List Sym} {n2 : ℕ}
    (hk : k = k2) (hk' : k' = k2') (hl : l = l2) (hl' : l' = l2') (hn : n = n2) :
    Win q q' k2 k2' l2 l2' n2 := by
  subst hk; subst hk'; subst hl; subst hl'; subst hn; exact h

/-- Splitting a run of `2`s. -/
lemma replicate_split (x : Sym) (i j : ℕ) :
    List.replicate (i + j) x = List.replicate i x ++ List.replicate j x :=
  List.replicate_add i j x

/-! ### Walking back along a run of `1`s -/

/-- One step: the head in state `B` on a `0` steps left onto the `1` next to it. -/
theorem win_B0_left : Win St.B St.A 1 0 [1, 0] [1, 0] 1 := Win.of_lrun (by decide)

/-- **The return sweep.**  Entering a run of `N` `1`s from the `0` at its right end in
state `B`, the head walks back to the `3` at its left end in exactly `N+1` steps, turning
every `1` into a `2`. -/
theorem onesBack (N : ℕ) :
    Win St.B St.A (N + 1) 0
      (3 :: (List.replicate N 1 ++ [0]))
      (3 :: (List.replicate N 2 ++ [0])) (N + 1) := by
  have hsw : Win St.A St.A N 0
      ((3 : Sym) :: (List.replicate N 1 ++ [0]))
      ((3 : Sym) :: (List.replicate N 2 ++ [0])) N := by
    have h := (Win.of_sweepL (run_ones_A N) 3).embed (by simp) [] [0]
    simpa using h
  cases N with
  | zero =>
      have h : Win St.B St.A 1 0 [(3 : Sym), 0] [(3 : Sym), 0] 1 := Win.of_lrun (by decide)
      simpa using h
  | succ n =>
      have hrep : ((3 : Sym) :: List.replicate n 1) ++ [1, 0] ++ []
          = (3 : Sym) :: (List.replicate (n + 1) 1 ++ [0]) := by
        rw [List.replicate_succ']
        simp
      have h1 : Win St.B St.A (n + 2) (n + 1)
          ((3 : Sym) :: (List.replicate (n + 1) 1 ++ [0]))
          ((3 : Sym) :: (List.replicate (n + 1) 1 ++ [0])) 1 := by
        have h := win_B0_left.embed (by simp) ((3 : Sym) :: List.replicate n 1) []
        exact h.cast (by simp) (by simp) hrep hrep rfl
      exact (h1.trans hsw rfl).cast rfl rfl rfl rfl (by omega)

/-! ### The turn-around at the right end of the run of `2`s -/

/-- The nine steps in which the head, having crossed the run of `2`s, turns around and
starts back. -/
theorem rule_endgame : Win St.A St.B 2 3 [0, 3, 2, 0] [1, 1, 1, 0] 9 :=
  Win.of_lrun (by decide)

/-! ### The repeated region -/

/-- **`cross_back`.**  A marker `1 0 3` sitting between a `3` and a run of `2n+1` twos
crosses the run and comes all the way back, in exactly `10n+14` steps; the run of `2`s has
grown to `2n+4`, and the marker has been consumed.  The cell beyond the run (the `0` at
the right of the window) is only read, never written. -/
theorem cross_back (n : ℕ) :
    Win St.A St.A 4 0
      ([3, 1, 0, 3] ++ (List.replicate (2 * n + 1) 2 ++ [0]))
      (3 :: (List.replicate (2 * n + 4) 2 ++ [0])) (10 * n + 14) := by
  -- the crossing
  have h1 := (pingpong_chain n).embed (by simp) [3] [0]
  -- the turn-around
  have h2 := rule_endgame.embed (by simp) ((3 : Sym) :: List.replicate (2 * n + 1) 1) []
  -- the return
  have h3 := onesBack (2 * n + 4)
  have eA : ([(3 : Sym)] ++ ([1, 0, 3] ++ List.replicate (2 * n + 1) 2)) ++ [0]
      = [3, 1, 0, 3] ++ (List.replicate (2 * n + 1) 2 ++ [0]) := by simp
  have eB : ([(3 : Sym)] ++ (List.replicate (2 * n + 1) 1 ++ [0, 3, 2])) ++ [0]
      = ((3 : Sym) :: List.replicate (2 * n + 1) 1) ++ [0, 3, 2, 0] ++ [] := by simp
  have eC : ((3 : Sym) :: List.replicate (2 * n + 1) 1) ++ [1, 1, 1, 0] ++ []
      = (3 : Sym) :: (List.replicate (2 * n + 4) 1 ++ [0]) := by
    have e : List.replicate (2 * n + 4) (1 : Sym) = List.replicate (2 * n + 1) 1 ++ [1, 1, 1] := by
      rw [show 2 * n + 4 = (2 * n + 1) + 3 from by ring, replicate_split]
      rfl
    rw [e]
    simp
  have H1 : Win St.A St.A 4 (2 * n + 4)
      ([3, 1, 0, 3] ++ (List.replicate (2 * n + 1) 2 ++ [0]))
      (((3 : Sym) :: List.replicate (2 * n + 1) 1) ++ [0, 3, 2, 0] ++ []) (8 * n) :=
    h1.cast (by simp) (by simp; omega) eA eB rfl
  have H2 : Win St.A St.B (2 * n + 4) (2 * n + 5)
      (((3 : Sym) :: List.replicate (2 * n + 1) 1) ++ [0, 3, 2, 0] ++ [])
      ((3 : Sym) :: (List.replicate (2 * n + 4) 1 ++ [0])) 9 :=
    h2.cast (by simp) (by simp) rfl eC rfl
  have H12 := H1.trans H2 (by simp)
  exact (H12.trans h3 (by simp)).cast rfl rfl rfl rfl (by omega)

/-! ### The fixed pieces of the two rules -/

theorem p1_phase1 :
    Win St.B St.A 3 16
      [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4, 2, 2]
      [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 1, 0, 3, 2] 19 :=
  Win.of_lrun (by decide)

theorem p1_mid : Win St.A St.A 3 5 [0, 0, 0, 3, 2, 2] [1, 3, 1, 0, 3, 2] 10 :=
  Win.of_lrun (by decide)

theorem p1_final :
    Win St.A St.B 10 0
      [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3]
      [0, 4, 4, 2, 2, 0, 4, 2, 0, 4, 4] 12 :=
  Win.of_lrun (by decide)

theorem p3_phase1 :
    Win St.B St.A 3 17
      [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4, 2, 2]
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 3, 2] 28 :=
  Win.of_lrun (by decide)

theorem p3_mid :
    Win St.A St.A 6 8 [0, 1, 0, 3, 1, 0, 3, 2, 2] [1, 3, 1, 0, 3, 1, 0, 3, 2] 14 :=
  Win.of_lrun (by decide)

theorem p3_final :
    Win St.A St.B 11 0
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3]
      [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] 11 :=
  Win.of_lrun (by decide)

/-! ### `P1 → P2` -/

/-- **The `P1` rule.**  The head is in state `B` on the leftmost non-blank cell, which
begins the token `U(2,1) = 0 4 4 2`; then come `U(4,1)` and `U(1,2m+2)`, and the three
cells to the left are blank.  In exactly `79 + 20m` steps the machine delivers a carry of
four `2`s to the third token and arrives, again in state `B`, on the new leftmost
non-blank cell three cells further left, the tape now reading `U(2,2) U(1,1) U(2,2m+6)`.
Nothing outside the window is read or written, so the rest of the tape is arbitrary. -/
theorem rule_P1 (m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * m + 6) ++ [0]) (79 + 20 * m) := by
  have r2 : ∀ i : ℕ, List.replicate (i + 2) (2 : Sym) = 2 :: 2 :: List.replicate i 2 := by
    intro i
    rw [show i + 2 = 2 + i from by ring, replicate_split]
    rfl
  have r1 : ∀ i : ℕ, List.replicate (i + 1) (2 : Sym) = 2 :: List.replicate i 2 := by
    intro i
    rw [show i + 1 = 1 + i from by ring, replicate_split]
    rfl
  -- step 1
  have h1 := p1_phase1.embed (by simp) [] (List.replicate (2 * m) 2 ++ [0])
  have e1in : ([] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4, 2, 2] ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = [0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++ [0] := by
    simp [tokU, r2 (2 * m)]
  have e1out : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 1, 0, 3, 2] ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
          ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    simp [r1 (2 * m)]
  have H1 : Win St.B St.A 3 16
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++ [0])
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ []) 19 :=
    h1.cast (by simp) (by simp) e1in e1out rfl
  -- step 2
  have h2 := (cross_back m).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] []
  have e2out : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3, 2, 2] ++
          (List.replicate (2 * m + 2) 2 ++ [0]) := by
    simp [r2 (2 * m + 2)]
  have H2 : Win St.A St.A 16 12
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [])
      ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3, 2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0])) (10 * m + 14) :=
    h2.cast (by simp) (by simp) rfl e2out rfl
  -- step 3
  have h3 := p1_mid.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    (List.replicate (2 * m + 2) 2 ++ [0])
  have e3out : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 3, 1, 0, 3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
          ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ [] := by
    simp [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring, r1 (2 * m + 2)]
  have H3 : Win St.A St.A 12 14
      ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3, 2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]))
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ []) 10 :=
    h3.cast (by simp) (by simp) rfl e3out rfl
  -- step 4
  have h4 := (cross_back (m + 1)).embed (by simp)
    [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] []
  have e4out : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
        (3 :: (List.replicate (2 * (m + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++
          (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp [show 2 * (m + 1) + 4 = 2 * m + 6 from by ring]
  have H4 : Win St.A St.A 14 10
      ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ [])
      ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0])) (10 * m + 24) :=
    h4.cast (by simp) (by simp) rfl e4out (by ring)
  -- step 5
  have h5 := p1_final.embed (by simp) [] (List.replicate (2 * m + 6) 2 ++ [0])
  have e5out : ([] ++ [0, 4, 4, 2, 2, 0, 4, 2, 0, 4, 4] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * m + 6) ++ [0] := by
    simp [tokU]
  have H5 : Win St.A St.B 10 0
      ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0]))
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * m + 6) ++ [0]) 12 :=
    h5.cast (by simp) (by simp) rfl e5out rfl
  have C1 := H1.trans H2 (by simp; omega)
  have C2 := C1.trans H3 (by simp; omega)
  have C3 := C2.trans H4 (by simp; omega)
  exact (C3.trans H5 (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### `P3 → P1` -/

/-- **The `P3` rule.**  From the prefix `U(2,2) V(1) U(1,1)` followed by `U(1,2m+2)`, the
machine reaches in exactly `91 + 20m` steps the configuration with prefix `U(2,1) U(4,1)`
followed by `U(1,2m+6)`, again in state `B` on the new leftmost non-blank cell.  Nothing
outside the window is read or written, so the rest of the tape is arbitrary. -/
theorem rule_P3 (m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 6) ++ [0]) (91 + 20 * m) := by
  have r2 : ∀ i : ℕ, List.replicate (i + 2) (2 : Sym) = 2 :: 2 :: List.replicate i 2 := by
    intro i
    rw [show i + 2 = 2 + i from by ring, replicate_split]
    rfl
  have r1 : ∀ i : ℕ, List.replicate (i + 1) (2 : Sym) = 2 :: List.replicate i 2 := by
    intro i
    rw [show i + 1 = 1 + i from by ring, replicate_split]
    rfl
  have h1 := p3_phase1.embed (by simp) [] (List.replicate (2 * m) 2 ++ [0])
  have e1in : ([] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4, 2, 2] ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = [0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0] := by
    simp [tokU, tokV, r2 (2 * m)]
  have e1out : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 3, 2] ++
        (List.replicate (2 * m) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0] ++
          ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [] := by
    simp [r1 (2 * m)]
  have H1 : Win St.B St.A 3 17
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ []) 28 :=
    h1.cast (by simp) (by simp) e1in e1out rfl
  have h2 := (cross_back m).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0] []
  have e2out : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0] ++
        (3 :: (List.replicate (2 * m + 4) 2 ++ [0])) ++ [] : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 1, 0, 3, 2, 2] ++
          (List.replicate (2 * m + 2) 2 ++ [0]) := by
    simp [r2 (2 * m + 2)]
  have H2 : Win St.A St.A 17 13
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * m + 1) 2 ++ [0])) ++ [])
      ([0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 1, 0, 3, 2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0])) (10 * m + 14) :=
    h2.cast (by simp) (by simp) rfl e2out rfl
  have h3 := p3_mid.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    (List.replicate (2 * m + 2) 2 ++ [0])
  have e3out : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 3, 1, 0, 3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
          ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ [] := by
    simp [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring, r1 (2 * m + 2)]
  have H3 : Win St.A St.A 13 15
      ([0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 1, 0, 3, 2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ [0]))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ []) 14 :=
    h3.cast (by simp) (by simp) rfl e3out rfl
  have h4 := (cross_back (m + 1)).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] []
  have e4out : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        (3 :: (List.replicate (2 * (m + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
          (List.replicate (2 * m + 6) 2 ++ [0]) := by
    simp [show 2 * (m + 1) + 4 = 2 * m + 6 from by ring]
  have H4 : Win St.A St.A 15 11
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (m + 1) + 1) 2 ++ [0])) ++ [])
      ([] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0])) (10 * m + 24) :=
    h4.cast (by simp) (by simp) rfl e4out (by ring)
  have h5 := p3_final.embed (by simp) [] (List.replicate (2 * m + 6) 2 ++ [0])
  have e5out : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (List.replicate (2 * m + 6) 2 ++ [0]) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 6) ++ [0] := by
    simp [tokU]
  have H5 : Win St.A St.B 11 0
      ([] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (List.replicate (2 * m + 6) 2 ++ [0]))
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 6) ++ [0]) 11 :=
    h5.cast (by simp) (by simp) rfl e5out rfl
  have C1 := H1.trans H2 (by simp; omega)
  have C2 := C1.trans H3 (by simp; omega)
  have C3 := C2.trans H4 (by simp; omega)
  exact (C3.trans H5 (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-! ### Non-halting over the duration of the two rules -/

/-- The machine does not halt while `rule_P1` is being applied. -/
theorem rule_P1_no_halt (m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 79 + 20 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1 m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

/-- The machine does not halt while `rule_P3` is being applied. -/
theorem rule_P3_no_halt (m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 91 + 20 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3 m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
