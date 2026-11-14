import RequestProject.TurnU2

/-!
# The carry absorbed by a token `U(2,b)`

The census of `ANALYSIS.md` §31 shows that the single most frequent macro step of the real
orbit that no rule of the development covered is the one in which the token that absorbs
the carry is `U(2,b) = 0 4 4 2^b` rather than `U(1,b) = 0 4 2^b`.  This file proves that
rule, in the phase `P3`, with arbitrary runs of `u = U(1,1)` on either side of the
absorbing token and an arbitrary even number of `2`s in it and in the last token:

```
0 0 0 · U(2,2) V(1) u · u^r · U(2,2m+4) · u^s · U(1,2m'+2) 0
          --(133 + 12r + 20m + 6s + 10m') steps-->
      U(2,1) U(4,1) · u^r · U(1,4) V(2m+1) · u^s · U(1,2m'+4) 0
```

So a token `U(2,b)` with `b = 2m+4` **splits** into `U(1,4) V(b-3)` and lets a carry of two
travel on to the next token with more than one `2`; the two tokens `U(1,·)` it produces
have between them exactly the cells of the old one, and the last token gains the two `2`s.
(The excluded case `b = 2` is the one that makes the machine halt; the orbit avoids it.)

The proof exhibits the computation as twenty-one macro steps.  Its new ingredient, beyond
the pieces of `TurnU2.lean`, is what happens on the **third** pass: after `turn_U2` has
turned the first pass around inside the absorbing token, and `turn_U2_second` has reflected
the second pass at the same token, the head runs rightwards over the *rest* of that token's
run of `2`s, and it is this third pass that delivers the carry of two to the last token.
Three small pieces describe it — `u2b_restart` (the head starts the third pass),
`u2b_exit` (the ping-pong reaches the end of the run and the head leaves it rightwards) and
`u2b_vturn` (on the way back the head turns the leftover `0` into the `4 3` that begins the
new token `V`) — together with `retL_1103`, the leftward crossing of the word `1 1 0 3` the
third pass leaves at the right end of the absorbing token.
-/

namespace BB25

/-! ### The four new pieces -/

/-- **The third pass starts.**  After the reflection `turn_U2_second` the head sits, in
state `B`, on the `3` of the marker `1 1 0 0 3`; in four steps it rewrites the marker as
`1 1 0 1 0 3` and enters the rest of the run of `2`s in state `A`. -/
theorem u2b_restart : Win St.B St.A 2 4 [0, 0, 3, 2, 2] [0, 1, 0, 3, 2] 4 :=
  Win.of_lrun (by decide)

/-- **The third pass leaves the run of `2`s.**  When the ping-pong marker `0 3` has only
two `2`s left in front of it, the eight steps of one more ping-pong unit exhaust the run and
put the head, in state `A`, on the `0` that begins the next token. -/
theorem u2b_exit : Win St.A St.A 2 4 [0, 3, 2, 2, 0] [1, 1, 0, 3, 0] 8 :=
  Win.of_lrun (by decide)

/-- **The `V` is created.**  Coming back leftwards over the cells the third pass turned
into `1`s, the head reaches the `0` that the first ping-pong step left behind; in four steps
it writes there the `4 3` that begins a token `V`, and turns around to continue leftwards. -/
theorem u2b_vturn : Win St.A St.A 0 0 [0, 2, 2] [1, 4, 3] 4 :=
  Win.of_lrun (by decide)

/-- **The leftward crossing of `1 1 0 3`.**  This is the word the third pass leaves at the
right end of the absorbing token; crossing it leftwards in state `A` takes four steps and
leaves `2 2 0 4`. -/
theorem retL_1103 : SweepL St.A St.A [1, 1, 0, 3] [2, 2, 0, 4] 4 := by
  have h1 : SweepL St.A St.A ([0] ++ [3]) ([0] ++ [4]) 2 :=
    sweepL_A3.comp sweepL_B0 (by simp)
  have h2 : SweepL St.A St.A ([1] ++ ([0] ++ [3])) ([2] ++ ([0] ++ [4])) 3 :=
    h1.comp sweepL_A1 (by simp)
  have h3 : SweepL St.A St.A ([1] ++ ([1] ++ ([0] ++ [3]))) ([2] ++ ([2] ++ ([0] ++ [4]))) 4 :=
    h2.comp sweepL_A1 (by simp)
  simpa using h3

/-- Moving one cell of a run of equal symbols across the boundary. -/
lemma replicate_cons_comm (x : Sym) (n : ℕ) (Y : List Sym) :
    x :: (List.replicate n x ++ Y) = List.replicate n x ++ x :: Y := by
  rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ', List.append_assoc]
  rfl

/-! ### The rule -/

/-- **The `P3` rule with an absorbing token `U(2,2m+4)`.**  The head is in state `B` on the
leftmost non-blank cell, with three blank cells to its left, and the tape reads

`U(2,2) V(1) U(1,1) · u^r · U(2,2m+4) · u^s · U(1,2m'+2)`

followed by the `0` of the next token.  In exactly `133 + 12r + 20m + 6s + 10m'` steps the
machine splits the token `U(2,2m+4)` into `U(1,4) V(2m+1)`, carries two `2`s past the `s`
tokens `u` into the last token, and arrives, again in state `B`, on the new leftmost
non-blank cell three cells further left.  Nothing outside the window is read or written. -/
theorem rule_P3_U2b (r m s mp : ℕ) :
    Win St.B St.B 3 0
      ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++ tokU 2 (2 * m + 4) ++
        rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0])
      (tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ tokV (2 * m + 1) ++
        rep (tokU 1 1) s ++ tokU 1 (2 * mp + 4) ++ [0])
      (133 + 12 * r + 20 * m + 6 * s + 10 * mp) := by
  -- splitting runs of `2`s and of `1`s
  have q4 : List.replicate (2 * m + 4) (2 : Sym) = [2, 2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 4 = 2 + (2 * m + 2) from by ring, replicate_split]; rfl
  have q3 : List.replicate (2 * m + 3) (2 : Sym) = [2] ++ List.replicate (2 * m + 2) 2 := by
    rw [show 2 * m + 3 = 1 + (2 * m + 2) from by ring, replicate_split]; rfl
  have q4' : List.replicate (2 * m + 4) (2 : Sym) = [2] ++ List.replicate (2 * m + 3) 2 := by
    rw [show 2 * m + 4 = 1 + (2 * m + 3) from by ring, replicate_split]; rfl
  have q3' : List.replicate (2 * m + 3) (2 : Sym) = [2, 2] ++ List.replicate (2 * m + 1) 2 := by
    rw [show 2 * m + 3 = 2 + (2 * m + 1) from by ring, replicate_split]; rfl
  have qones : (1 : Sym) :: List.replicate (2 * m) 1 = List.replicate (2 * m) 1 ++ [1] := by
    rw [← List.replicate_succ, show ([1] : List Sym) = List.replicate 1 1 from rfl,
      ← List.replicate_add]
  have qones' : List.replicate (2 * m) (1 : Sym) ++ [1] = List.replicate (2 * m + 1) 1 := by
    rw [show ([1] : List Sym) = List.replicate 1 1 from rfl, ← List.replicate_add]
  have qmp : List.replicate (2 * mp + 2) (2 : Sym) = [2, 2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 2 = 2 + 2 * mp from by ring, replicate_split]; rfl
  have qmp' : List.replicate (2 * mp + 1) (2 : Sym) = [2] ++ List.replicate (2 * mp) 2 := by
    rw [show 2 * mp + 1 = 1 + 2 * mp from by ring, replicate_split]; rfl
  -- the block `U(2,·)` crossed rightwards
  have hblk : SweepR St.A St.A ([0, 4, 4, 2] : List Sym) [1, 0, 0, 3] 4 := by
    simpa [blkIn, blkOut] using blockR 2
  -- stage A : the opening
  have HA := carry_open.embed (by simp) []
    ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))))
  -- stage B : the carry crosses the run of `u`s
  have HB := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (r + 1)) (by simp) 0).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3]
    ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))))
  -- stage C : the head enters the absorbing token
  have HC := (Win.of_sweepR hblk (by simp) 2).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1))
    (List.replicate (2 * m + 2) 2 ++
      (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))
  -- stage D : the first pass turns around inside the absorbing token
  have HD := (turn_U2 (m + 1)).embed (by simp) ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++
    rep [1, 0, 3] (r + 1))
    (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))
  -- stage E : the return across what it left behind
  have HE := (Win.of_sweepL retU2 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0])
    (List.replicate (2 * m + 3) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))
  -- stage F : back across the run of `u`s
  have HF := (Win.of_sweepL (sweepL_bulk (r + 1)) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 0, 1, 0]
    ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  -- stage G : the reflection at the `4`-run of the prefix
  have HG := carry_reflect.embed (by simp) [0, 1, 3, 1, 0, 1, 1]
    ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))))))
  -- stage H : the second pass crosses the run of `u`s
  have HH := (Win.of_sweepR (sweepR_rep sweepR_204 (by simp) (r + 1)) (by simp) 2).embed
    (by simp) [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))))
  -- stage I : the second pass is reflected at the absorbing token
  have HI := turn_U2_second.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1])
    (List.replicate (2 * m + 3) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))
  -- stage J : the third pass starts
  have HJ := u2b_restart.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1])
    (List.replicate (2 * m + 1) 2 ++
      (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))
  -- stage K : the ping-pong across the rest of the run
  have HK := (pingpong_chain0 m).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1])
    ([2] ++ (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))
  -- stage L : the third pass leaves the run
  have HL := u2b_exit.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
      List.replicate (2 * m) 1)
    (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))
  -- stage M : the third pass crosses the second run of `u`s
  have HM := (Win.of_sweepR (sweepR_rep sweepR_042 (by simp) (s + 1)) (by simp) 2).embed
    (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0, 3])
    (List.replicate (2 * mp) 2 ++ [0])
  -- stage N : the carry of two is delivered to the last token
  have HN := (cross_back mp).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] s) []
  -- stage O : back across the second run of `u`s
  have HO := (Win.of_sweepL (sweepL_bulk s) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
      List.replicate (2 * m) 1 ++ [1, 1, 0])
    (List.replicate (2 * mp + 4) 2 ++ [0])
  -- stage P : back across the word the third pass left at the absorbing token
  have HP := (Win.of_sweepL retL_1103 1).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0] ++
      List.replicate (2 * m) 1)
    (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))
  -- stage Q : back across the cells the third pass turned into `1`s
  have HQ := (Win.of_sweepL (run_ones_A (2 * m + 1)) 0).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1])
    ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))
  -- stage R : the new token `V` is created
  have HR := u2b_vturn.embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1])
    (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
      (List.replicate (2 * mp + 4) 2 ++ [0]))))
  -- stage S : the last four cells of the old token
  have HS := (Win.of_sweepL (run_ones_A 4) 3).embed (by simp)
    ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r)
    ([4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
      (List.replicate (2 * mp + 4) 2 ++ [0])))))
  -- stage T : the last leftward crossing of the run of `u`s
  have HT := (Win.of_sweepL (sweepL_bulk r) 3).embed (by simp)
    [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0]
    ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
      (List.replicate (2 * mp + 4) 2 ++ [0])))))
  -- stage U : the closing
  have HU := p3_final.embed (by simp) []
    (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++
      ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))))
  -- the tape words the computation passes through
  have E0 : ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++
        tokU 2 (2 * m + 4) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0] : List Sym)
      = [] ++ [0, 0, 0, 0, 4, 4, 2, 2, 4, 3, 2, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))))) := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl, rep_succ]
    simp [tokU, tokV]
  have E1 : ([] ++ [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3, 0] ++
        ([4, 2] ++ (rep [0, 4, 2] r ++ ([0, 4, 4] ++ (List.replicate (2 * m + 4) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0]))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [0, 4, 2] (r + 1) ++ [0]) ++
        ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [rep_succ]; simp
  have E2 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ (rep [1, 0, 3] (r + 1) ++ [0]) ++
        ([4, 4] ++ (List.replicate (2 * m + 4) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([0, 4, 4, 2] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])))) := by
    rw [q4]; simp
  have Etail : (rep [0, 4, 2] s ++ ([0, 4] ++ (List.replicate (2 * mp + 2) 2 ++ [0])) : List Sym)
      = 0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [rep_shift']; simp
  have E3 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([1, 0, 0, 3] ++ [2]) ++
        (List.replicate (2 * m + 2) 2 ++
          (rep [0, 4, 2] s ++ ([0, 4] ++
            (List.replicate (2 * mp + 2) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([1, 0, 0, 3] ++ List.replicate (2 * (m + 1) + 1) 2 ++ [0]) ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    rw [Etail, show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, q3]; simp
  have E4 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] (r + 1)) ++
        ([1, 1, 3] ++ List.replicate (2 * (m + 1) + 2) 2 ++ [0]) ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [1, 1, 3, 2]) ++
        (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 from by ring, q4', rep_succ']; simp
  have E5 : (([0, 1, 3, 1, 0, 1, 1, 0, 1, 0, 3] ++ rep [1, 0, 3] r ++ [1, 0]) ++
        (3 :: [2, 2, 4, 3]) ++
        (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [1, 0, 3] (r + 1)) ++
        ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    rw [rep_succ']; simp
  have E6 : ([0, 1, 3, 1, 0, 1, 1, 0, 1, 0] ++ (3 :: rep [2, 0, 4] (r + 1)) ++
        ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1] ++ [0, 1, 0, 3, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))))) := by
    rw [rep_succ]; simp
  have E7 : ([0, 1, 3, 1, 0, 1, 1] ++ [1, 3, 1, 0, 2] ++
        ([0, 4] ++ (rep [2, 0, 4] r ++ ([2, 2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [2, 0, 4] (r + 1) ++ [2]) ++
        ([2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))) := by
    rw [rep_succ]; simp
  have E8 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (rep [3, 1, 0] (r + 1) ++ [2]) ++
        ([2, 4, 3] ++ (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0])))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [0, 2, 2, 4, 3] ++
        (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [rep_succ']; simp
  have E9 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1]) ++
        [1, 1, 0, 0, 3] ++
        (List.replicate (2 * m + 3) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        [0, 0, 3, 2, 2] ++
        (List.replicate (2 * m + 1) 2 ++
          (0 :: (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    rw [q3']; simp
  have E10 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        [0, 1, 0, 3, 2] ++
        (List.replicate (2 * m + 1) 2 ++
          (0 :: (rep [4, 2, 0] s ++
            (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1]) ++
        ([0, 3] ++ List.replicate (2 * m + 1) 2) ++
        ([2] ++ (0 :: (rep [4, 2, 0] s ++
          (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) := by
    simpa using replicate_cons_comm 2 (2 * m + 1) _
  have E11 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++
          [3, 1, 1, 1, 0, 1]) ++ (List.replicate (2 * m) 1 ++ [0, 3, 2]) ++
        ([2] ++ (0 :: (rep [4, 2, 0] s ++
          (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1) ++ [0, 3, 2, 2, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) := by
    simp
  have E12 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1) ++ [1, 1, 0, 3, 0] ++
        (rep [4, 2, 0] s ++ (4 :: (List.replicate (2 * mp + 2) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 3]) ++ (rep [0, 4, 2] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) := by
    rw [rep_succ', qmp]; simp [rep_shift']
  have E13 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0, 3]) ++ (rep [1, 0, 3] (s + 1) ++ [2]) ++
        (List.replicate (2 * mp) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] s) ++
        ([3, 1, 0, 3] ++ (List.replicate (2 * mp + 1) 2 ++ [0])) ++ [] := by
    rw [rep_succ, qmp']; simp [rep_shift']
  have E14 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0] ++ rep [3, 1, 0] s) ++
        (3 :: (List.replicate (2 * mp + 4) 2 ++ [0])) ++ [] : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0]) ++ (3 :: rep [1, 0, 3] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) := by
    simp [rep_shift']
  have E15 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0, 1] ++
          List.replicate (2 * m) 1 ++ [1, 1, 0]) ++ (3 :: rep [2, 0, 4] s) ++
        (List.replicate (2 * mp + 4) 2 ++ [0]) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0] ++
          List.replicate (2 * m) 1) ++ (1 :: [1, 1, 0, 3]) ++
        (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])) := by
    simp [qones]
  have E16 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1, 0] ++
          List.replicate (2 * m) 1) ++ (1 :: [2, 2, 0, 4]) ++
        (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        (0 :: List.replicate (2 * m + 1) 1) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))) := by
    simp [← qones']
  have E17 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        (0 :: List.replicate (2 * m + 1) 2) ++
        ([2, 2, 0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0]))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        [0, 2, 2] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) := by
    simp [replicate_cons_comm 2 (2 * m + 1)]
  have E18 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r ++ [3, 1, 1, 1]) ++
        [1, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0])))) : List Sym)
      = ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        (3 :: List.replicate 4 1) ++
        ([4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    simp
  have E19 : (([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ rep [3, 1, 0] r) ++
        (3 :: List.replicate 4 2) ++
        ([4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++ (rep [2, 0, 4] s ++
          (List.replicate (2 * mp + 4) 2 ++ [0]))))) : List Sym)
      = [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [1, 0, 3] r) ++
        ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++
          (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) := by
    simp [rep_shift']
  have E20 : ([0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0] ++ (3 :: rep [2, 0, 4] r) ++
        ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++ ([0, 4] ++
          (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0]))))) : List Sym)
      = [] ++ [0, 1, 3, 1, 0, 1, 1, 1, 3, 1, 0, 3] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++ (List.replicate (2 * mp + 4) 2 ++ [0])))))) := by
    simp
  have E21 : ([] ++ [0, 4, 4, 2, 0, 4, 4, 4, 4, 2, 0, 4] ++
        (rep [2, 0, 4] r ++ ([2, 2, 2, 2, 4, 3] ++ (List.replicate (2 * m + 1) 2 ++
          ([0, 4] ++ (rep [2, 0, 4] s ++
            (List.replicate (2 * mp + 4) 2 ++ [0])))))) : List Sym)
      = tokU 2 1 ++ tokU 4 1 ++ rep (tokU 1 1) r ++ tokU 1 4 ++ tokV (2 * m + 1) ++
        rep (tokU 1 1) s ++ tokU 1 (2 * mp + 4) ++ [0] := by
    rw [show tokU 1 1 = ([0, 4, 2] : List Sym) from rfl]
    simp [tokU, tokV, rep_shift']
  -- chain the stages
  have SA : Win St.B St.A 3 11 _ _ 22 :=
    HA.cast (by simp) (by simp) E0.symm E1 rfl
  have SB : Win St.A St.A 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HB.cast (by simp) (by simp; ring) rfl E2 (by ring)
  have SC : Win St.A St.A (3 * r + 14) (3 * r + 18) _ _ 4 :=
    HC.cast (by simp; omega) (by simp; omega) rfl E3 rfl
  have SD : Win St.A St.A (3 * r + 18) (3 * r + 17) _ _ (10 * m + 25) :=
    HD.cast (by simp; omega) (by simp; omega) rfl E4 (by ring)
  have SE : Win St.A St.A (3 * r + 17) (3 * r + 13) _ _ 4 :=
    HE.cast (by simp; omega) (by simp; omega) rfl E5 rfl
  have SF : Win St.A St.A (3 * r + 13) 10 _ _ (3 * r + 3) :=
    HF.cast (by simp; omega) (by simp) rfl E6 (by ring)
  have SG : Win St.A St.B 10 11 _ _ 7 :=
    HG.cast (by simp) (by simp) rfl E7 rfl
  have SH : Win St.B St.B 11 (3 * r + 14) _ _ (3 * r + 3) :=
    HH.cast (by simp) (by simp; ring) rfl E8 (by ring)
  have SI : Win St.B St.B (3 * r + 14) (3 * r + 17) _ _ 9 :=
    HI.cast (by simp; omega) (by simp; omega) rfl E9 rfl
  have SJ : Win St.B St.A (3 * r + 17) (3 * r + 19) _ _ 4 :=
    HJ.cast (by simp; omega) (by simp; omega) rfl E10 rfl
  have SK : Win St.A St.A (3 * r + 19) (3 * r + 2 * m + 19) _ _ (8 * m) :=
    HK.cast (by simp; omega) (by simp; omega) rfl E11 rfl
  have SL : Win St.A St.A (3 * r + 2 * m + 19) (3 * r + 2 * m + 21) _ _ 8 :=
    HL.cast (by simp; omega) (by simp; omega) rfl E12 rfl
  have SM : Win St.A St.A (3 * r + 2 * m + 21) (3 * r + 2 * m + 3 * s + 24) _ _
      (3 * s + 3) :=
    HM.cast (by simp; omega) (by simp; omega) rfl E13 (by ring)
  have SN : Win St.A St.A (3 * r + 2 * m + 3 * s + 24) (3 * r + 2 * m + 3 * s + 20) _ _
      (10 * mp + 14) :=
    HN.cast (by simp; omega) (by simp; omega) rfl E14 rfl
  have SO : Win St.A St.A (3 * r + 2 * m + 3 * s + 20) (3 * r + 2 * m + 20) _ _ (3 * s) :=
    HO.cast (by simp; omega) (by simp; omega) rfl E15 (by ring)
  have SP : Win St.A St.A (3 * r + 2 * m + 20) (3 * r + 2 * m + 16) _ _ 4 :=
    HP.cast (by simp; omega) (by simp; omega) rfl E16 rfl
  have SQ : Win St.A St.A (3 * r + 2 * m + 16) (3 * r + 15) _ _ (2 * m + 1) :=
    HQ.cast (by simp; omega) (by simp; omega) rfl E17 rfl
  have SR : Win St.A St.A (3 * r + 15) (3 * r + 15) _ _ 4 :=
    HR.cast (by simp; omega) (by simp; omega) rfl E18 rfl
  have SS : Win St.A St.A (3 * r + 15) (3 * r + 11) _ _ 4 :=
    HS.cast (by simp; omega) (by simp; omega) rfl E19 rfl
  have ST : Win St.A St.A (3 * r + 11) 11 _ _ (3 * r) :=
    HT.cast (by simp; omega) (by simp) rfl E20 (by ring)
  have SU : Win St.A St.B 11 0 _ _ 11 :=
    HU.cast (by simp) (by simp) rfl E21 rfl
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
  have T11 := T10.trans SL (by simp; omega)
  have T12 := T11.trans SM (by simp; omega)
  have T13 := T12.trans SN (by simp; omega)
  have T14 := T13.trans SO (by simp; omega)
  have T15 := T14.trans SP (by simp; omega)
  have T16 := T15.trans SQ (by simp; omega)
  have T17 := T16.trans SR (by simp; omega)
  have T18 := T17.trans SS (by simp; omega)
  have T19 := T18.trans ST (by simp; omega)
  exact (T19.trans SU (by simp; omega)).cast rfl rfl rfl rfl (by ring)

/-- The machine does not halt while `rule_P3_U2b` is being applied. -/
theorem rule_P3_U2b_no_halt (r m s mp : ℕ) (T : ℤ → Sym) (a : ℤ)
    (hs : Seg T a ([0, 0, 0] ++ tokU 2 2 ++ tokV 1 ++ rep (tokU 1 1) (r + 1) ++
      tokU 2 (2 * m + 4) ++ rep (tokU 1 1) s ++ tokU 1 (2 * mp + 2) ++ [0])) :
    ∀ i ≤ 133 + 12 * r + 20 * m + 6 * s + 10 * mp,
      ¬ Halted (step^[i] ⟨St.B, a + 3, T⟩) := by
  have := (rule_P3_U2b r m s mp).no_halt (by exact fun h => St.noConfusion h) T a hs
  simpa using this

end BB25
