import RequestProject.CarryV

/-!
# The `P1` carry handed across a token `V`

`CarryV.lean` proved the rule in which a token `V` follows the token that the carry
reaches, in the phase `P3`.  This file proves the corresponding rule in the phase `P1`,
which is the one the real orbit actually uses:

```
0 0 0 · U(2,1) U(4,1) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2) 0
       --(171 + 20m + 20c + 12s + 20m') steps-->
   U(2,2) u · U(2,2m+6) · V(2c+1) · u^s · U(1,2m'+6) 0
```

As always in the phase `P1` the exponent `a` of the first token after the prefix is raised
by one — here that token is the absorbing one, so `U(1,2m+2)` becomes `U(2,2m+6)` — and as
in `CarryV.lean` the carry is not stopped by the `V`: the ping-pong marker walks straight
through it, so the four extra `2`s are taken from the `V` and handed on to the last token.

The middle of the computation is literally the middle of `rule_P3_V`: the same eleven
pieces are crossed in the same order on each of the machine's two passes.  What differs is
the opening (`p1g_open`, the `P1` prefix `U(2,1) U(4,1)` instead of `U(2,2) V(1)`), the
turn-around at the left end (`p1g_reflect`, `p1g_B4`) and the closing, for which two new
five- and seven-step pieces are needed.  The computation is exhibited as twenty-nine macro
steps.
-/

namespace BB25

/-! ### The two new pieces -/

/-- **The last `u` is rebuilt.**  Coming back leftwards in state `A` at the left end of the
region, the head turns the `0 3 1 0 1 3` that the second pass left into `0 4 2 0 4 4` — the
token `u` and the beginning of the raised token — and arrives in state `B` at the left end
of that word. -/
theorem p1v_back : Win St.A St.B 5 0 [0, 3, 1, 0, 1, 3] [0, 4, 2, 0, 4, 4] 5 :=
  Win.of_lrun (by decide)

/-- **The closing `7` steps.**  The head rebuilds the prefix `U(2,2)` and stops on the new
leftmost non-blank cell in state `B`. -/
theorem p1v_close : Win St.B St.B 5 0 [0, 1, 3, 1, 0, 0] [0, 4, 4, 2, 2, 0] 7 :=
  Win.of_lrun (by decide)

/-! ### The rule -/

set_option maxHeartbeats 2000000 in
/-- **The `P1` rule with a `V` after the absorbing token.**  The head is in state `B` on
the leftmost non-blank cell, with three blank cells to its left, and the tape reads

`U(2,1) U(4,1) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2)`

followed by the `0` of the next token.  In exactly `171 + 20m + 20c + 12s + 20m'` steps the
absorbing token becomes `U(2,2m+6)`, the `V(2c+5)` becomes `V(2c+1)` and the last token
becomes `U(1,2m'+6)`; the head arrives, again in state `B`, on the new leftmost non-blank
cell three cells further left.  Nothing outside the window is read or written. -/
theorem rule_P1_V (m c s mp : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++
        tokV (2 * c + 5) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0])
      (tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * m + 6) ++
        tokV (2 * c + 1) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 6) ++ [0])
      (171 + 20 * m + 20 * c + 12 * s + 20 * mp) := by
  -- splitting the runs
  have hz2m2 : List.replicate (2 * m + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 2 = 2 + 2 * m from by ring, replicate_split]; rfl
  have hz2m3 : List.replicate (2 * m + 3) (2 : Sym)
      = [2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  have hz2m4 : List.replicate (2 * m + 4) (2 : Sym)
      = [2] ++ List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  have hz2c5 : List.replicate (2 * c + 5) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * c + 3) 2 := by
    rw [show 2 * c + 5 = 2 + (2 * c + 3) from by ring, replicate_split]; rfl
  have hz2c3 : List.replicate (2 * c + 3) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * c + 1) 2 := by
    rw [show 2 * c + 3 = 2 + (2 * c + 1) from by ring, replicate_split]; rfl
  have hzmp2 : List.replicate (2 * mp + 2) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 2 = 2 + 2 * mp from by ring, replicate_split]; rfl
  have hzmp1 : List.replicate (2 * mp + 1) (2 : Sym)
      = [2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 1 = 1 + 2 * mp from by ring, replicate_split]; rfl
  have hzmp4 : List.replicate (2 * mp + 4) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * mp + 2) 2 := by
    rw [show 2 * mp + 4 = 2 + (2 * mp + 2) from by ring, replicate_split]; rfl
  have hzmp3 : List.replicate (2 * (mp + 1) + 1) (2 : Sym)
      = [2] ++ List.replicate (2 * mp + 2) 2 := by
    rw [show 2 * (mp + 1) + 1 = 1 + (2 * mp + 2) from by ring, replicate_split]; rfl
  have ho2c5 : List.replicate (2 * c + 5) (1 : Sym)
      = [1] ++ (List.replicate (2 * c + 2) 1 ++ [1, 1]) := by
    rw [show 2 * c + 5 = 1 + ((2 * c + 2) + 2) from by ring, replicate_split, replicate_split]
    rfl
  have ho2c3 : List.replicate (2 * c + 3) (1 : Sym)
      = [1] ++ (List.replicate (2 * c) 1 ++ [1, 1]) := by
    rw [show 2 * c + 3 = 1 + ((2 * c) + 2) from by ring, replicate_split, replicate_split]
    rfl
  have ho2m4 : List.replicate (2 * m + 4) (1 : Sym)
      = [1] ++ (List.replicate (2 * m) 1 ++ [1, 1, 1]) := by
    rw [show 2 * m + 4 = 1 + ((2 * m) + 3) from by ring, replicate_split, replicate_split]
    rfl
  have ho2m6 : List.replicate (2 * m + 6) (1 : Sym)
      = [1] ++ (List.replicate (2 * m + 2) 1 ++ [1, 1, 1]) := by
    rw [show 2 * m + 6 = 1 + ((2 * m + 2) + 3) from by ring, replicate_split, replicate_split]
    rfl
  have hz2m1 : List.replicate (2 * m + 1) (2 : Sym) = [2] ++ List.replicate (2 * m) 2 := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring, replicate_split]; rfl
  have Etail : (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))
        : List Sym)
      = 0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [rep_shift']; simp
  -- the twenty-nine stages
  have HA := p1g_open.embed (by simp) []
    ([4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))
  have HB := (Win.of_sweepR sweepR_042 (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3]
    (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  have HC1 := (pingpong_chain0 m).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1])
    ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))
  have HC2 := vcross_step.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1)
    (List.replicate (2 * c + 3) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have HC3 := (pingpong_chain0 (c + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1])
    ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  have HC4 := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1)
    (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))
  have HD := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp) 2 ++ [0])
  have HE := (cross_back mp).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0] ++
      rep [3, 1, 0] s) []
  have HF := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 4) 2 ++ [0])
  have HG := (Win.of_sweepL retV 1).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1])
    (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
  have HH := (Win.of_sweepL (run_ones_A (2 * c + 5)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1])
    ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have HI := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
      List.replicate (2 * m) 1 ++ [1, 1])
    (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HJ := (Win.of_sweepL (run_ones_A (2 * m + 4)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0])
    ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
  have HK1 := p1g_reflect.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0]
    (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HK2 := p1g_B4.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1]
    (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HO := carry_B2.embed (by simp) [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0]
    (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  have HP := (pingpong_chain0 (m + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1])
    ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
  have HQ := vcross_step.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1)
    (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HR := (pingpong_chain0 c).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1])
    ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
  have HS := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1)
    ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  have HT := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp + 2) 2 ++ [0])
  have HU := (cross_back (mp + 1)).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0] ++
      rep [3, 1, 0] s) []
  have HV := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 6) 2 ++ [0])
  have HW := (Win.of_sweepL retV 1).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1])
    (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
  have HX := (Win.of_sweepL (run_ones_A (2 * c + 3)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1])
    ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
  have HY := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
      List.replicate (2 * m + 2) 1 ++ [1, 1])
    (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))
  have HZ := (Win.of_sweepL (run_ones_A (2 * m + 6)) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1])
    ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
  have HAA := p1v_back.embed (by simp) [0, 1, 3, 1, 0]
    (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
  have HAB := p1v_close.embed (by simp) []
    ([4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
      (List.replicate (2 * c + 1) 2 ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++
        tokV (2 * c + 5) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0] ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 5) 2 ++
            (rep [0, 4, 2] s ++ ([0, 4] ++
              (List.replicate (2 * mp + 2) 2 ++ [0]))))))) := by
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3, 0] ++
        ([4] ++ (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 5) 2 ++
            (rep [0, 4, 2] s ++ ([0, 4] ++
              (List.replicate (2 * mp + 2) 2 ++ [0]))))))) : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ ([0, 4, 2] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    rw [hz2m2]; simp
  have E2 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ ([1, 0, 3] ++ [2]) ++
        (List.replicate (2 * m) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0])))))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1]) ++
        ([0, 3] ++ List.replicate (2 * m + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [hz2m1]; simp
  have E3 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1]) ++
        (List.replicate (2 * m) 1 ++ [0, 3, 2]) ++
        ([4, 3] ++ (List.replicate (2 * c + 5) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1) ++ [0, 3, 2, 4, 3, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E4 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1) ++ [1, 1, 0, 1, 0, 3, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * c + 3) 2) ++
        ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++
          (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    simpa using replicate_cons_comm 2 (2 * c + 3) _
  have E5 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1]) ++
        (List.replicate (2 * c + 2) 1 ++ [0, 3, 2]) ++
        ([2] ++ (rep [0, 4, 2] s ++ ([0, 4] ++
          (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1) ++
        [0, 3, 2, 2, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [Etail]; simp
  have E6 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1) ++
        [1, 1, 0, 3, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) := by
    rw [rep_succ' ([0, 4, 2] : List Sym) s, hzmp2]; simp [rep_shift']
  have E7 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * mp + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ ([1, 0, 3] : List Sym) s, hzmp1]; simp [rep_shift']
  have E8 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        (3 :: (List.replicate (2 * mp + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0]) ++ (3 :: rep [1, 0, 3] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) := by
    simp [rep_shift']
  have E9 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++
          [1, 1, 0]) ++ (3 :: rep [2, 0, 4] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1]) ++
        [1, 0, 3] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])) := by
    simp
  have E10 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c + 2) 1 ++ [1]) ++
        [1, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ (0 :: List.replicate (2 * c + 5) 1) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    rw [ho2c5]; simp
  have E11 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ (0 :: List.replicate (2 * c + 5) 2) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ [0, 2, 2] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    rw [hz2c5]; simp
  have E12 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0, 3] ++ [1] ++
          List.replicate (2 * m) 1 ++ [1, 1]) ++ [1, 4, 3] ++
        (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
        (3 :: List.replicate (2 * m + 4) 1) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    rw [ho2m4]; simp
  have E13 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 0, 0, 0] ++
        (3 :: List.replicate (2 * m + 4) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [0, 0, 0, 3] ++
        (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    simp
  have E14 : ([0, 1, 3, 1, 0, 0, 3, 1, 0] ++ [1, 3, 1, 4] ++
        (List.replicate (2 * m + 4) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [4, 2] ++
        (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    rw [hz2m4]; simp
  have E15 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++ [0, 2] ++
        (List.replicate (2 * m + 3) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ [2, 2] ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    rw [hz2m3]; simp
  have E16 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1, 0] ++ [3, 2] ++
        (List.replicate (2 * m + 2) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
        ([0, 3] ++ List.replicate (2 * (m + 1) + 1) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, hz2m3]
    simp
  have E17 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
        (List.replicate (2 * (m + 1)) 1 ++ [0, 3, 2]) ++
        ([4, 3] ++ (List.replicate (2 * c + 3) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1) ++ [0, 3, 2, 4, 3, 2, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, hz2c3]; simp
  have E18 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1) ++ [1, 1, 0, 1, 0, 3, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * c + 1) 2) ++
        ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    simpa using replicate_cons_comm 2 (2 * c + 1) _
  have E19 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1]) ++
        (List.replicate (2 * c) 1 ++ [0, 3, 2]) ++
        ([2] ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1) ++
        [0, 3, 2, 2, 0] ++
        ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    simp
  have E20 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1) ++
        [1, 1, 0, 3, 0] ++
        ([4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp + 2) 2 ++ [0]) := by
    rw [rep_succ' ([0, 4, 2] : List Sym) s, hzmp4]; simp [rep_shift']
  have E21 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp + 2) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * (mp + 1) + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ ([1, 0, 3] : List Sym) s, hzmp3]; simp [rep_shift']
  have E22 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0] ++ rep [3, 1, 0] s) ++
        (3 :: (List.replicate (2 * (mp + 1) + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0]) ++ (3 :: rep [1, 0, 3] s) ++
        (List.replicate (2 * mp + 6) 2 ++ [0]) := by
    rw [show 2 * (mp + 1) + 4 = 2 * mp + 6 from by ring]; simp [rep_shift']
  have E23 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++
          [1, 1, 0]) ++ (3 :: rep [2, 0, 4] s) ++
        (List.replicate (2 * mp + 6) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1]) ++
        [1, 0, 3] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])) := by
    simp
  have E24 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1, 0, 1] ++ List.replicate (2 * c) 1 ++ [1]) ++
        [1, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: List.replicate (2 * c + 3) 1) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))) := by
    rw [ho2c3]; simp
  have E25 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++
        (0 :: List.replicate (2 * c + 3) 2) ++
        ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))
          : List Sym)
      = ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++ [0, 2, 2] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))) := by
    rw [hz2c3]; simp
  have E26 : (([0, 1, 3, 1, 0, 0, 3, 1, 0, 1, 3, 1] ++
          List.replicate (2 * m + 2) 1 ++ [1, 1]) ++ [1, 4, 3] ++
        (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))
          : List Sym)
      = [0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
        (3 :: List.replicate (2 * m + 6) 1) ++
        ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))) := by
    rw [ho2m6]; simp
  have E27 : ([0, 1, 3, 1, 0, 0, 3, 1, 0, 1] ++
        (3 :: List.replicate (2 * m + 6) 2) ++
        ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))
          : List Sym)
      = [0, 1, 3, 1, 0] ++ [0, 3, 1, 0, 1, 3] ++
        (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0])))))) := by
    simp
  have E28 : ([0, 1, 3, 1, 0] ++ [0, 4, 2, 0, 4, 4] ++
        (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++ (List.replicate (2 * c + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 6) 2 ++ [0]))))))
          : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 0] ++
        ([4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 1) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 6) 2 ++ [0]))))))) := by
    simp
  have E29 : ([] ++ [0, 4, 4, 2, 2, 0] ++
        ([4, 2, 0, 4, 4] ++ (List.replicate (2 * m + 6) 2 ++ ([4, 3] ++
          (List.replicate (2 * c + 1) 2 ++
            ([0, 4] ++ (rep [2, 0, 4] s ++
              (List.replicate (2 * mp + 6) 2 ++ [0]))))))) : List Sym)
      = tokU 2 2 ++ tokU 1 1 ++ tokU 2 (2 * m + 6) ++
        tokV (2 * c + 1) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 6) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 13 _ _ 16 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 13 16 _ _ 3 :=
    HB.cast (by simp) (by simp) rfl E2 rfl
  have SC1 : Win St.A St.A 16 (2 * m + 16) _ _ (8 * m) :=
    HC1.cast (by simp) (by simp; omega) rfl E3 rfl
  have SC2 : Win St.A St.A (2 * m + 16) (2 * m + 20) _ _ 12 :=
    HC2.cast (by simp) (by simp) rfl E4 rfl
  have SC3 : Win St.A St.A (2 * m + 20) (2 * m + 2 * c + 22) _ _ (8 * c + 8) :=
    HC3.cast (by simp) (by simp; omega) rfl E5 (by ring)
  have SC4 : Win St.A St.A (2 * m + 2 * c + 22) (2 * m + 2 * c + 24) _ _ 8 :=
    HC4.cast (by simp; omega) (by simp; omega) rfl E6 rfl
  have SD : Win St.A St.A (2 * m + 2 * c + 24)
      (2 * m + 2 * c + 3 * s + 27) _ _ (3 * s + 3) :=
    HD.cast (by simp; omega) (by simp; omega) rfl E7 (by ring)
  have SE : Win St.A St.A (2 * m + 2 * c + 3 * s + 27)
      (2 * m + 2 * c + 3 * s + 23) _ _ (10 * mp + 14) :=
    HE.cast (by simp; omega) (by simp; omega) rfl E8 rfl
  have SF : Win St.A St.A (2 * m + 2 * c + 3 * s + 23)
      (2 * m + 2 * c + 23) _ _ (3 * s) :=
    HF.cast (by simp; omega) (by simp; omega) rfl E9 (by ring)
  have SG : Win St.A St.A (2 * m + 2 * c + 23) (2 * m + 2 * c + 21) _ _ 2 :=
    HG.cast (by simp; omega) (by simp; omega) rfl E10 rfl
  have SH : Win St.A St.A (2 * m + 2 * c + 21) (2 * m + 16) _ _ (2 * c + 5) :=
    HH.cast (by simp; omega) (by simp) rfl E11 rfl
  have SI : Win St.A St.A (2 * m + 16) (2 * m + 16) _ _ 4 :=
    HI.cast (by simp) (by simp) rfl E12 rfl
  have SJ : Win St.A St.A (2 * m + 16) 12 _ _ (2 * m + 4) :=
    HJ.cast (by simp; omega) (by simp) rfl E13 rfl
  have SK1 : Win St.A St.B 12 12 _ _ 8 :=
    HK1.cast (by simp) (by simp) rfl E14 rfl
  have SK2 : Win St.B St.B 12 13 _ _ 1 :=
    HK2.cast (by simp) (by simp) rfl E15 rfl
  have SO : Win St.B St.A 13 14 _ _ 1 :=
    HO.cast (by simp) (by simp) rfl E16 rfl
  have SP : Win St.A St.A 14 (2 * m + 16) _ _ (8 * m + 8) :=
    HP.cast (by simp) (by simp; omega) rfl E17 (by ring)
  have SQ : Win St.A St.A (2 * m + 16) (2 * m + 20) _ _ 12 :=
    HQ.cast (by simp) (by simp) rfl E18 rfl
  have SR : Win St.A St.A (2 * m + 20) (2 * m + 2 * c + 20) _ _ (8 * c) :=
    HR.cast (by simp) (by simp; omega) rfl E19 rfl
  have SS : Win St.A St.A (2 * m + 2 * c + 20) (2 * m + 2 * c + 22) _ _ 8 :=
    HS.cast (by simp; omega) (by simp; omega) rfl E20 rfl
  have ST : Win St.A St.A (2 * m + 2 * c + 22)
      (2 * m + 2 * c + 3 * s + 25) _ _ (3 * s + 3) :=
    HT.cast (by simp; omega) (by simp; omega) rfl E21 (by ring)
  have SU : Win St.A St.A (2 * m + 2 * c + 3 * s + 25)
      (2 * m + 2 * c + 3 * s + 21) _ _ (10 * mp + 24) :=
    HU.cast (by simp; omega) (by simp; omega) rfl E22 (by ring)
  have SV : Win St.A St.A (2 * m + 2 * c + 3 * s + 21)
      (2 * m + 2 * c + 21) _ _ (3 * s) :=
    HV.cast (by simp; omega) (by simp; omega) rfl E23 (by ring)
  have SW : Win St.A St.A (2 * m + 2 * c + 21) (2 * m + 2 * c + 19) _ _ 2 :=
    HW.cast (by simp; omega) (by simp; omega) rfl E24 rfl
  have SX : Win St.A St.A (2 * m + 2 * c + 19) (2 * m + 16) _ _ (2 * c + 3) :=
    HX.cast (by simp; omega) (by simp) rfl E25 rfl
  have SY : Win St.A St.A (2 * m + 16) (2 * m + 16) _ _ 4 :=
    HY.cast (by simp) (by simp) rfl E26 rfl
  have SZ : Win St.A St.A (2 * m + 16) 10 _ _ (2 * m + 6) :=
    HZ.cast (by simp; omega) (by simp) rfl E27 rfl
  have SAA : Win St.A St.B 10 5 _ _ 5 :=
    HAA.cast (by simp) (by simp) rfl E28 rfl
  have SAB : Win St.B St.B 5 0 _ _ 7 :=
    HAB.cast (by simp) (by simp) rfl E29 rfl
  have T1 := SA.trans SB (by simp; omega)
  have T2 := T1.trans SC1 (by simp; omega)
  have T3 := T2.trans SC2 (by simp; omega)
  have T4 := T3.trans SC3 (by simp; omega)
  have T5 := T4.trans SC4 (by simp; omega)
  have T6 := T5.trans SD (by simp; omega)
  have T7 := T6.trans SE (by simp; omega)
  have T8 := T7.trans SF (by simp; omega)
  have T9 := T8.trans SG (by simp; omega)
  have T10 := T9.trans SH (by simp; omega)
  have T11 := T10.trans SI (by simp; omega)
  have T12 := T11.trans SJ (by simp; omega)
  have T13 := T12.trans SK1 (by simp; omega)
  have T14 := T13.trans SK2 (by simp; omega)
  have T15 := T14.trans SO (by simp; omega)
  have T16 := T15.trans SP (by simp; omega)
  have T17 := T16.trans SQ (by simp; omega)
  have T18 := T17.trans SR (by simp; omega)
  have T19 := T18.trans SS (by simp; omega)
  have T20 := T19.trans ST (by simp; omega)
  have T21 := T20.trans SU (by simp; omega)
  have T22 := T21.trans SV (by simp; omega)
  have T23 := T22.trans SW (by simp; omega)
  have T24 := T23.trans SX (by simp; omega)
  have T25 := T24.trans SY (by simp; omega)
  have T26 := T25.trans SZ (by simp; omega)
  have T27 := T26.trans SAA (by simp; omega)
  exact (T27.trans SAB (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P1_V` is being applied. -/
theorem rule_P1_V_no_halt (m c s mp : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 1 ++ tokU 4 1 ++ tokU 1 (2 * m + 2) ++
      tokV (2 * c + 5) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0])) :
    ∀ i ≤ 171 + 20 * m + 20 * c + 12 * s + 20 * mp,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P1_V m c s mp).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
