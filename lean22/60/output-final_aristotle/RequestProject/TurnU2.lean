import RequestProject.FlatP1

/-!
# The turn-around at an absorbing token `U(2,b)`

Every macro rule proved so far assumes that the token which absorbs the carry is
`U(1,b) = 0 4 2^b`.  The census of `ANALYSIS.md` §31 shows that the most frequent shape the
real orbit actually presents is an absorbing token `U(2,b) = 0 4 4 2^b`, and §32 states the
corresponding macro rule.  This file proves the piece of that rule which is genuinely new:
the **turn-around inside the run of `2`s when the marker left by the rightward sweep is
`1 0 0 3` instead of `1 0 3`**.

```
1 0 0 3 · 2^(2M+1) · 0     --(10M+15 steps)-->     1 1 3 · 2^(2M+2) · 0
```

(the head enters on the first `2` of the run and leaves on the first `2` of the new run, in
state `A` both times).  Unlike `cross_back`, which deposits four `2`s and sends the head
back out to the left, this turn-around deposits only one `2` and leaves the head *inside*
the region: an absorbing token with `a = 2` therefore needs two more passes, which is why
it ends up as `U(1,4) V(b−3)` rather than as `U(1,b+4)`.

The two other new pieces of that rule are proved here as well: `retU2`, the leftward return
across what the turn-around left behind, and `turn_U2_second`, the point at which the
second pass is reflected.

Along the way the ping-pong chain and the return sweep are generalised so that the cell to
the left of the marker may carry *any* symbol (in `LeftRules.lean` and `Cycle.lean` it has
to be a `1` resp. a `3`); that cell is never read, so the generalisation is free, and it is
exactly what is needed here, where it carries a `0`.
-/

namespace BB25

/-! ### The ping-pong chain, with an arbitrary cell to the left of the marker -/

/-- The ping-pong unit, with the cell to the left of the marker removed from the window:
the marker `0 3` travels two cells into the run of `2`s in `8` steps. -/
theorem pingpong_unit0 : Win St.A St.A 2 4 [0, 3, 2, 2, 2] [1, 1, 0, 3, 2] 8 :=
  Win.of_lrun (by decide)

lemma pp_list (n : ℕ) :
    [(0 : Sym), 3] ++ List.replicate (2 * n + 3) 2
      = ([0, 3, 2, 2, 2] : List Sym) ++ List.replicate (2 * n) 2 := by
  rw [show 2 * n + 3 = 3 + 2 * n from by ring, List.replicate_add]
  simp

lemma pp_list' (n : ℕ) :
    ([1, 1] : List Sym) ++ ([0, 3] ++ List.replicate (2 * n + 1) 2)
      = ([1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2 := by
  rw [show 2 * n + 1 = 1 + 2 * n from by ring, List.replicate_add]
  simp

/-- **The ping-pong chain** in the form in which the cell to the left of the marker is not
part of the window: the marker `0 3` crosses `2n` cells of a run of `2`s in exactly `8n`
steps, turning them into `1`s. -/
theorem pingpong_chain0 (n : ℕ) :
    Win St.A St.A 2 (2 * n + 2)
      ([0, 3] ++ List.replicate (2 * n + 1) 2)
      (List.replicate (2 * n) 1 ++ [0, 3, 2]) (8 * n) := by
  induction n with
  | zero => simpa using Win.refl St.A 2 ([0, 3] ++ List.replicate 1 2)
  | succ n ih =>
      have e1 : 2 * (n + 1) + 2 = 2 * n + 4 := by ring
      have e2 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
      have e3 : 8 * (n + 1) = 8 + 8 * n := by ring
      rw [e1, e2, e3]
      have h1 : Win St.A St.A 2 4
          ([0, 3] ++ List.replicate (2 * n + 3) 2)
          (([1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2) 8 := by
        have := pingpong_unit0.embed (by simp) [] (List.replicate (2 * n) 2)
        simpa [pp_list n] using this
      have h2 : Win St.A St.A 4 (2 * n + 4)
          (([1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2)
          (([1, 1] : List Sym) ++ (List.replicate (2 * n) 1 ++ [0, 3, 2])) (8 * n) := by
        have h := ih.embed (by simp) [1, 1] []
        rw [pp_list' n] at h
        have ek : ([1, 1] : List Sym).length + 2 = 4 := by simp
        have ek' : ([1, 1] : List Sym).length + (2 * n + 2) = 2 * n + 4 := by simp; ring
        rw [ek, ek'] at h
        simpa using h
      have hlen : (([1, 1, 0, 3, 2] : List Sym) ++ List.replicate (2 * n) 2).length
          = ([0, 3] ++ List.replicate (2 * n + 3) 2 : List Sym).length := by
        simp only [List.length_append, List.length_replicate, List.length_cons,
          List.length_nil]
        omega
      have hc := h1.trans h2 hlen
      have hl : ([1, 1] : List Sym) ++ (List.replicate (2 * n) 1 ++ [0, 3, 2])
          = List.replicate (2 * n + 2) 1 ++ [0, 3, 2] := by
        rw [show 2 * n + 2 = 2 + 2 * n from by ring,
          List.replicate_add 2 (2 * n) (1 : Sym), List.append_assoc]
        rfl
      rw [hl] at hc
      exact hc

/-! ### The return sweep, with an arbitrary stopping cell -/

/-- One step: the head in state `B` on a `0` steps left onto the cell next to it, whatever
that cell contains. -/
theorem win_B0_left_gen (x : Sym) : Win St.B St.A 1 0 [x, 0] [x, 0] 1 := by
  fin_cases x <;> exact Win.of_lrun (by decide)

/-- **The return sweep**, with an arbitrary cell at the far end: entering a run of `N` `1`s
from the `0` at its right end in state `B`, the head walks back to the cell at its left end
in exactly `N+1` steps, turning every `1` into a `2`.  That cell is reached but never read,
so it may carry any symbol (`onesBack` is the case `x = 3`). -/
theorem onesBack_gen (x : Sym) (N : ℕ) :
    Win St.B St.A (N + 1) 0
      (x :: (List.replicate N 1 ++ [0]))
      (x :: (List.replicate N 2 ++ [0])) (N + 1) := by
  have hsw : Win St.A St.A N 0
      (x :: (List.replicate N 1 ++ [0]))
      (x :: (List.replicate N 2 ++ [0])) N := by
    have h := (Win.of_sweepL (run_ones_A N) x).embed (by simp) [] [0]
    simpa using h
  cases N with
  | zero => simpa using win_B0_left_gen x
  | succ n =>
      have hrep : (x :: List.replicate n 1) ++ [1, 0] ++ []
          = x :: (List.replicate (n + 1) 1 ++ [0]) := by
        rw [List.replicate_succ']
        simp
      have h1 : Win St.B St.A (n + 2) (n + 1)
          (x :: (List.replicate (n + 1) 1 ++ [0]))
          (x :: (List.replicate (n + 1) 1 ++ [0])) 1 := by
        have h := win_B0_left.embed (by simp) (x :: List.replicate n 1) []
        exact h.cast (by simp) (by simp) hrep hrep rfl
      exact (h1.trans hsw rfl).cast rfl rfl rfl rfl (by omega)

/-! ### The turn-around -/

/-- The two steps in which, after the return sweep, the head turns the leftover `0` into
the marker `1 3` and steps back into the run of `2`s. -/
theorem turn_U2_restart : Win St.A St.A 1 3 [1, 0, 2, 2] [1, 1, 3, 2] 2 :=
  Win.of_lrun (by decide)

/-- **The turn-around at an absorbing token `U(2,b)`.**  The rightward sweep across the
block `0 4 4 2` of such a token leaves the marker `1 0 0 3` — one `0` more than the marker
`1 0 3` that a token `U(1,b)` leaves — and the head on the first of the remaining `2`s.
The head then crosses the run of `2`s and comes back, but the extra `0` stops the return
sweep one cell early, so that instead of leaving the region (as in `cross_back`) the head
turns around again and re-enters the run.  In exactly `10M+15` steps a run of `2M+1` `2`s
becomes a run of `2M+2` `2`s, the marker is reduced to `1 1 3`, and the head is back on the
first `2` of the new run in state `A`.  The cell beyond the run is only read. -/
theorem turn_U2 (M : ℕ) :
    Win St.A St.A 4 3
      ([1, 0, 0, 3] ++ List.replicate (2 * M + 1) 2 ++ [0])
      ([1, 1, 3] ++ List.replicate (2 * M + 2) 2 ++ [0])
      (10 * M + 15) := by
  have q3 : List.replicate (2 * M + 3) (1 : Sym)
      = List.replicate (2 * M) 1 ++ [1, 1, 1] := by
    rw [show 2 * M + 3 = 2 * M + 3 from rfl,
      show (2 * M + 3) = (2 * M) + 3 from by ring, List.replicate_add]
    rfl
  have q4 : List.replicate (2 * M + 3) (2 : Sym)
      = [2, 2] ++ List.replicate (2 * M + 1) 2 := by
    rw [show 2 * M + 3 = 2 + (2 * M + 1) from by ring, List.replicate_add]
    rfl
  have q5 : List.replicate (2 * M + 2) (2 : Sym)
      = [2] ++ List.replicate (2 * M + 1) 2 := by
    rw [show 2 * M + 2 = 1 + (2 * M + 1) from by ring, List.replicate_add]
    rfl
  -- stage 1 : the ping-pong across the run of `2`s
  have H1 := (pingpong_chain0 M).embed (by simp) [1, 0] [0]
  -- stage 2 : the turn-around at the far end of the run
  have H2 := rule_endgame.embed (by simp) ([1, 0] ++ List.replicate (2 * M) 1) []
  -- stage 3 : the return sweep, stopped by the extra `0`
  have H3 := (onesBack_gen 0 (2 * M + 3)).embed (by simp) [1] []
  -- stage 4 : the head turns around again
  have H4 := turn_U2_restart.embed (by simp) [] (List.replicate (2 * M + 1) 2 ++ [0])
  have E0 : ([1, 0, 0, 3] ++ List.replicate (2 * M + 1) 2 ++ [0] : List Sym)
      = [1, 0] ++ ([0, 3] ++ List.replicate (2 * M + 1) 2) ++ [0] := by simp
  have E1 : ([1, 0] ++ (List.replicate (2 * M) 1 ++ [0, 3, 2]) ++ [0] : List Sym)
      = ([1, 0] ++ List.replicate (2 * M) 1) ++ [0, 3, 2, 0] ++ [] := by simp
  have E2 : (([1, 0] ++ List.replicate (2 * M) 1) ++ [1, 1, 1, 0] ++ [] : List Sym)
      = [1] ++ ((0 : Sym) :: (List.replicate (2 * M + 3) 1 ++ [0])) ++ [] := by
    rw [q3]; simp
  have E3 : ([1] ++ ((0 : Sym) :: (List.replicate (2 * M + 3) 2 ++ [0])) ++ [] : List Sym)
      = [] ++ [1, 0, 2, 2] ++ (List.replicate (2 * M + 1) 2 ++ [0]) := by
    rw [q4]; simp
  have E4 : ([] ++ [1, 1, 3, 2] ++ (List.replicate (2 * M + 1) 2 ++ [0]) : List Sym)
      = [1, 1, 3] ++ List.replicate (2 * M + 2) 2 ++ [0] := by
    rw [q5]; simp
  have S1 : Win St.A St.A 4 (2 * M + 4) _ _ (8 * M) :=
    H1.cast (by simp) (by simp; ring) E0.symm E1 rfl
  have S2 : Win St.A St.B (2 * M + 4) (2 * M + 5) _ _ 9 :=
    H2.cast (by simp) (by simp) rfl E2 rfl
  have S3 : Win St.B St.A (2 * M + 5) 1 _ _ (2 * M + 4) :=
    H3.cast (by simp; omega) (by simp) rfl E3 (by ring)
  have S4 : Win St.A St.A 1 3 _ _ 2 :=
    H4.cast (by simp) (by simp) rfl E4 rfl
  have T1 := S1.trans S2 (by simp)
  have T2 := T1.trans S3 (by simp)
  exact (T2.trans S4 (by simp)).cast rfl rfl rfl rfl (by ring)

/-! ### The two remaining new pieces of the `U(2,b)` rule -/

/-- **The leftward return after the turn-around.**  What `turn_U2` leaves behind, `1 1 3`
followed by the run of `2`s, is crossed leftwards in state `A` in `4` steps and becomes
`2 2 4 3`; the head emerges on the left, in state `A`, ready to run back to the prefix over
the blocks `1 0 3`. -/
theorem retU2 : SweepL St.A St.A [1, 1, 3, 2] [2, 2, 4, 3] 4 := by
  have h1 : SweepL St.A St.A ([3] ++ [2]) ([4] ++ [3]) 2 :=
    sweepL_A2.comp sweepL_B3 (by simp)
  have h2 : SweepL St.A St.A ([1] ++ ([3] ++ [2])) ([2] ++ ([4] ++ [3])) 3 :=
    h1.comp sweepL_A1 (by simp)
  have h3 : SweepL St.A St.A ([1] ++ ([1] ++ ([3] ++ [2]))) ([2] ++ ([2] ++ ([4] ++ [3]))) 4 :=
    h2.comp sweepL_A1 (by simp)
  simpa using h3

/-- **The reflection of the second pass at an absorbing token `U(2,b)`.**  The second pass,
running rightwards in state `B`, meets the word `2 2 4 3` that the first pass left at the
absorbing token and is turned around by it in `9` steps, leaving `1 1 0 0 3`; this is the
analogue, for an absorbing token with `a = 2`, of `u21_turn`. -/
theorem turn_U2_second : Win St.B St.B 1 4 [0, 2, 2, 4, 3] [1, 1, 0, 0, 3] 9 :=
  Win.of_lrun (by decide)

end BB25
