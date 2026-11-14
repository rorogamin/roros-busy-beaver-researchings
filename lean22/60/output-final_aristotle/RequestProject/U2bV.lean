import RequestProject.ExcGen

/-!
# The `P3` row with a `V` after an absorbing `U(2,8)`

This file proves the second of the two rows that `ANALYSIS.md` §36 left open: the `P3`
configuration whose absorbing token is `U(2,8)` and which carries a `V(1)` immediately
after it.  For all `t, m`:

```
0 0 0 · U(2,2) V(1) u · U(2,8) V(1) · u^(t+3) · U(1,2m+2) 0
       --(433 + 30t + 50m) steps-->
   U(2,1) U(4,1) · u u · U(2,2) V(1) · u^(t+1) · U(1,2m+12) 0
```

The head makes **five** passes over the region.  The computation splits into six *fixed*
stretches, in which the head stays inside the first twenty-nine cells — where the tape
does not depend on `t` or `m`, so each stretch is a single kernel computation — and five
*excursions* into the run of `u`s and the token beyond it.  Each excursion is a chain of
the sweeps, ping-pongs and turn-arounds the project already provides, and none of them
looks at the tape left of the cell where it starts; that is why they can be stated
without mentioning the fixed part at all.
-/

namespace BB25

/-! ### The five excursions

Each is an instance of one of the three general excursions of `ExcGen.lean`, stated on a
window that begins one cell to the left of the run of `u`s; the head enters at offset `1`
and comes back to offset `0`, so nothing further left is touched. -/

/-- **Excursion 1.**  The carry crosses the whole run of `u`s, is absorbed by the token
beyond it and comes back. -/
theorem u2bv_exc1 (t m : ℕ) :
    Win St.A St.A 1 0
      ([3] ++ rep [0, 4, 2] (t + 4) ++ (List.replicate (2 * m + 1) 2 ++ [0]))
      ([3] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0]))
      (6 * t + 10 * m + 35) :=
  (exc_A042 (t + 3) m).cast rfl rfl rfl rfl (by ring)

/-- **Excursion 2.**  The head crosses the run of `u`s again, this time in state `B`; the
carry is passed on inside the run of `2`s and the head returns. -/
theorem u2bv_exc2 (t m : ℕ) :
    Win St.B St.B 1 0
      ([0] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0]))
      ([0] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      (6 * t + 10 * m + 41) :=
  (exc_B204 (t + 2) m).cast rfl rfl rfl rfl (by ring)

/-- **Excursion 3.**  The third pass, in which the head enters the region in state `B` on
a `4`. -/
theorem u2bv_exc3 (t m : ℕ) :
    Win St.B St.A 1 0
      ([1] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))
      ([1] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0]))
      (6 * t + 10 * m + 47) :=
  (exc_C420 (t + 1) m).cast rfl rfl rfl rfl (by ring)

/-- **Excursion 4.**  The fourth pass; like the first, the carry is absorbed by the run of
`2`s and the head comes straight back. -/
theorem u2bv_exc4 (t m : ℕ) :
    Win St.A St.A 1 0
      ([3] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0]))
      ([3] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0]))
      (6 * t + 10 * m + 53) :=
  (exc_A042 (t + 1) (m + 3)).cast rfl rfl
    (by rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by ring])
    (by rw [show 2 * (m + 3) + 4 = 2 * m + 10 from by ring]) (by ring)

/-- **Excursion 5.**  The last pass; the head leaves the region for good. -/
theorem u2bv_exc5 (t m : ℕ) :
    Win St.B St.B 1 0
      ([0] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0]))
      ([0] ++ rep [4, 2, 0] t ++ ([4] ++ (List.replicate (2 * m + 12) 2 ++ [0])))
      (6 * t + 10 * m + 59) :=
  (exc_B204 t (m + 3)).cast rfl rfl
    (by rw [show 2 * (m + 3) + 4 = 2 * m + 10 from by ring])
    (by rw [show 2 * (m + 3) + 6 = 2 * m + 12 from by ring]) (by ring)

/-! ### The six fixed stretches

In each of these the head stays inside the first twenty-nine cells, where the tape does
not depend on `t` or `m`; so each is a single kernel computation. -/

/-- The opening stretch: sixty-five steps that rewrite the head of the configuration. -/
theorem u2bv_fix0 :
    Win St.B St.A 3 28
      [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 4, 3, 2, 0]
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 3, 0]
      65 :=
  Win.of_lrun (by decide)

/-- The second stretch: seven steps between the first and the second excursion. -/
theorem u2bv_fix1 :
    Win St.A St.B 27 28
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 3, 2]
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 0, 2]
      7 :=
  Win.of_lrun (by decide)

/-- The third stretch: forty-one steps between the second and the third excursion. -/
theorem u2bv_fix2 :
    Win St.B St.B 27 28
      [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 0, 4]
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 4]
      41 :=
  Win.of_lrun (by decide)

/-- The fourth stretch: eleven steps between the third and the fourth excursion. -/
theorem u2bv_fix3 :
    Win St.A St.A 27 28
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0]
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 3, 0]
      11 :=
  Win.of_lrun (by decide)

/-- The fifth stretch: seventeen steps between the fourth and the fifth excursion. -/
theorem u2bv_fix4 :
    Win St.A St.B 27 28
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 3, 2]
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1, 0, 2]
      17 :=
  Win.of_lrun (by decide)

/-- The closing stretch: fifty-seven steps that carry the head back to cell `0`. -/
theorem u2bv_fix5 :
    Win St.B St.B 27 0
      [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1, 0, 4]
      [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4, 2, 0, 4, 2, 0, 4, 4, 2, 2, 4, 3, 2, 0, 4, 2, 0, 4]
      57 :=
  Win.of_lrun (by decide)

/-! ### The row -/

/-- Rotating a whole period of a `3`-periodic run past the run. -/
lemma u2bv_rot3 (a b c : Sym) (k : ℕ) (X : List Sym) :
    a :: b :: c :: (rep [a, b, c] k ++ X) = rep [a, b, c] k ++ (a :: b :: c :: X) := by
  rw [show (a :: b :: c :: (rep [a, b, c] k ++ X)) = [a, b, c] ++ (rep [a, b, c] k ++ X) from rfl,
    ← List.append_assoc, ← rep_succ, rep_succ', List.append_assoc]
  rfl

/-- **The `P3` row with an absorbing `U(2,8)` followed by a `V`.**  For all `t` and `m`,

```
0 0 0 . U(2,2) V(1) u . U(2,8) V(1) . u^(t+3) . U(1,2m+2) 0
   --(433 + 30t + 50m) steps-->
       U(2,1) U(4,1) . u u . U(2,2) V(1) . u^(t+1) . U(1,2m+12) 0
```
-/
theorem rule_P3_U2b_V (t m : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++
        rep (tokU 1 1) (t + 3) ++ tokU 1 (2 * m + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
        rep (tokU 1 1) (t + 1) ++ tokU 1 (2 * m + 12) ++ [0])
      (433 + 30 * t + 50 * m) := by
  have q2 : List.replicate (2 * m + 2) (2 : Sym) = 2 :: List.replicate (2 * m + 1) 2 := by
    rw [show 2 * m + 2 = 1 + (2 * m + 1) from by ring,
      replicate_split (2 : Sym) 1 (2 * m + 1)]; rfl
  have H0 : Win St.B St.A 3 28
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++
        rep (tokU 1 1) (t + 3) ++ tokU 1 (2 * m + 2) ++ [0])
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] ++
        ([3] ++ rep [0, 4, 2] (t + 4) ++ (List.replicate (2 * m + 1) 2 ++ [0]))) 65 :=
    (u2bv_fix0.embed (by simp) [] ([4, 2] ++ rep [0, 4, 2] (t + 3) ++ (List.replicate (2 * m + 1) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [tokU, tokV, q2]; exact u2bv_rot3 0 4 2 (t + 3) _) (by simp [rep_succ (w := [0, 4, 2]) (t + 3)]) rfl
  have H1 : Win St.A St.A 28 27
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] ++
        ([3] ++ rep [0, 4, 2] (t + 4) ++ (List.replicate (2 * m + 1) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] ++
        ([3] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0]))) (6 * t + 10 * m + 35) :=
    ((u2bv_exc1 t m).embed (by simp; omega) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] []).cast (by simp) (by simp)
      (by simp) (by simp) rfl
  have H2 : Win St.A St.B 27 28
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] ++
        ([3] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] ++
        ([0] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0]))) 7 :=
    (u2bv_fix1.embed (by simp) [] ([0, 4] ++ rep [2, 0, 4] (t + 2) ++ (List.replicate (2 * m + 4) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [rep_succ (w := [2, 0, 4]) (t + 2)]) (by simp [rep_succ (w := [2, 0, 4]) (t + 2)]) rfl
  have H3 : Win St.B St.B 28 27
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] ++
        ([0] ++ rep [2, 0, 4] (t + 3) ++ (List.replicate (2 * m + 4) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] ++
        ([0] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) (6 * t + 10 * m + 41) :=
    ((u2bv_exc2 t m).embed (by simp; omega) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] []).cast (by simp) (by simp)
      (by simp) (by simp) rfl
  have H4 : Win St.B St.B 27 28
      ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 1, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] ++
        ([0] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] ++
        ([1] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0])))) 41 :=
    (u2bv_fix2.embed (by simp) [] (rep [2, 0, 4] (t + 2) ++ (List.replicate (2 * m + 6) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [rep_shift' 4 2 0 (t + 2)]) (by simp [rep_shift' 4 2 0 (t + 2)]) rfl
  have H5 : Win St.B St.A 28 27
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] ++
        ([1] ++ rep [4, 2, 0] (t + 2) ++ ([4] ++ (List.replicate (2 * m + 6) 2 ++ [0]))))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] ++
        ([1] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0]))) (6 * t + 10 * m + 47) :=
    ((u2bv_exc3 t m).embed (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] []).cast (by simp) (by simp)
      (by simp) (by simp) rfl
  have H6 : Win St.A St.A 27 28
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] ++
        ([1] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] ++
        ([3] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0]))) 11 :=
    (u2bv_fix3.embed (by simp) [] ([4, 2] ++ rep [0, 4, 2] (t + 1) ++ (List.replicate (2 * m + 7) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [rep_succ (w := [0, 4, 2]) (t + 1)]) (by simp [rep_succ (w := [0, 4, 2]) (t + 1)]) rfl
  have H7 : Win St.A St.A 28 27
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] ++
        ([3] ++ rep [0, 4, 2] (t + 2) ++ (List.replicate (2 * m + 7) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] ++
        ([3] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0]))) (6 * t + 10 * m + 53) :=
    ((u2bv_exc4 t m).embed (by simp; omega) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] []).cast (by simp) (by simp)
      (by simp) (by simp) rfl
  have H8 : Win St.A St.B 27 28
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] ++
        ([3] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1] ++
        ([0] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0]))) 17 :=
    (u2bv_fix4.embed (by simp) [] ([0, 4] ++ rep [2, 0, 4] t ++ (List.replicate (2 * m + 10) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [rep_succ (w := [2, 0, 4]) t]) (by simp [rep_succ (w := [2, 0, 4]) t]) rfl
  have H9 : Win St.B St.B 28 27
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1] ++
        ([0] ++ rep [2, 0, 4] (t + 1) ++ (List.replicate (2 * m + 10) 2 ++ [0])))
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1] ++
        ([0] ++ rep [4, 2, 0] t ++ ([4] ++ (List.replicate (2 * m + 12) 2 ++ [0])))) (6 * t + 10 * m + 59) :=
    ((u2bv_exc5 t m).embed (by simp; omega) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1] []).cast (by simp) (by simp)
      (by simp) (by simp) rfl
  have H10 : Win St.B St.B 27 0
      ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3, 1, 0, 3, 1, 0, 0, 0, 0, 1, 3, 1, 0, 0, 3, 1] ++
        ([0] ++ rep [4, 2, 0] t ++ ([4] ++ (List.replicate (2 * m + 12) 2 ++ [0]))))
      (tokU 2 1 ++ tokU 4 1 ++ tokU 1 1 ++ tokU 1 1 ++ tokU 2 2 ++ tokV 1 ++
        rep (tokU 1 1) (t + 1) ++ tokU 1 (2 * m + 12) ++ [0]) 57 :=
    (u2bv_fix5.embed (by simp) [] (rep [2, 0, 4] t ++ (List.replicate (2 * m + 12) 2 ++ [0]))).cast (by simp) (by simp)
      (by simp [rep_shift' 4 2 0 t]) (by simp [tokU, tokV, rep_succ (w := [0, 4, 2]) t, rep_shift2 0 4 2 t]) rfl
  have C0 := H0.trans H1 (by simp; omega)
  have C1 := C0.trans H2 (by simp; omega)
  have C2 := C1.trans H3 (by simp; omega)
  have C3 := C2.trans H4 (by simp; omega)
  have C4 := C3.trans H5 (by simp; omega)
  have C5 := C4.trans H6 (by simp; omega)
  have C6 := C5.trans H7 (by simp; omega)
  have C7 := C6.trans H8 (by simp; omega)
  have C8 := C7.trans H9 (by simp; omega)
  have C9 := C8.trans H10 (by simp; omega)
  exact C9.cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U2b_V` is being applied. -/
theorem rule_P3_U2b_V_no_halt (t m : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ tokU 1 1 ++ tokU 2 8 ++ tokV 1 ++
      rep (tokU 1 1) (t + 3) ++ tokU 1 (2 * m + 2) ++ [0])) :
    ∀ i ≤ 433 + 30 * t + 50 * m, ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U2b_V t m).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
