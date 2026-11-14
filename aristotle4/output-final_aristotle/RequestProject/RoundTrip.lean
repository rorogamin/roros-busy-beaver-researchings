import RequestProject.Macro

/-!
# The round trip: one complete cycle of the head

`Macro.lean` proves the individual macroscopic rules (outward pass, turn, return
sweep, counter increment).  This file glues them into the **round trip**, the
unit out of which the whole computation between two structural events is built:

> the head leaves the counter, crosses the region to the right of it, turns
> around at the first `4 2` that is preceded by a `0` or a `2`, sweeps back over
> the cells it has just written, and increments the counter.

`round_trip` states this as a single theorem, with the exact number of steps and
the exact resulting tape.  Its content is the *region map*: if the region word
is `w ++ 4 :: 2 :: r` and the outward pass rewrites `w` as `w'` with
`w'.reverse = p :: t`, then after one round trip the region word is

```
(t.map sweepSym).reverse ++ sweepSym p :: 4 :: 4 :: r
```

and the counter has gone up by one.  Two facts about the coupling of the two
halves of the tape fall out of this:

* the **phase** in which the outward pass starts is the least significant digit
  of the counter (`3 ↦` phase `3`, `4 ↦` phase `4`, `0 ↦` phase `0`), so the
  counter really does drive the region; and
* the pass can change that digit (rules `four_two_of_three`, `four_two_of_four`
  turn it into the next digit up), so the region drives the counter as well.
  This is the exact two-way interface asked for in `ANALYSIS.md` §4.5.

Any non-halting invariant must be a set of region words closed under the map
above (§5.8); `round_trip` is the induction step such a proof would use.
-/

namespace TM2x5

/-- **Turn and sweep.**  The head, in state `A` on a cell `4` followed by a `2`,
with a `0` or a `2` on its left, turns around (`A_turn`) and sweeps back over
the block `t` of `0`/`2` cells, coming to rest in state `B` on the first cell
`q` that is neither a `0` nor a `2` — in practice the least significant digit of
the counter.  The crossed cells are rewritten by `0 ↦ 2`, `2 ↦ 4`, and the two
cells `4 2` at the turning point become `4 4`. -/
theorem turn_and_sweep (p : Sym) (hp : p = 0 ∨ p = 2) (t : List Sym)
    (ht : ∀ s ∈ t, s = 0 ∨ s = 2) (q : Sym) (m r : List Sym) :
    iter (4 + t.length) (some ⟨St.A, p :: (t ++ q :: m), 4, (2 : Sym) :: r⟩) =
      some ⟨St.B, m, q,
        (t.map sweepSym).reverse ++ sweepSym p :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
  cases t with
  | nil =>
    simpa using A_turn p hp q m r
  | cons c t0 =>
    have hc : c = 0 ∨ c = 2 := ht c (List.mem_cons_self ..)
    have ht0 : ∀ s ∈ t0, s = 0 ∨ s = 2 := fun s hs => ht s (List.mem_cons_of_mem _ hs)
    have h1 : iter 4 (some (⟨St.A, p :: ((c :: t0) ++ q :: m), 4, (2 : Sym) :: r⟩ : Cfg)) =
        some ⟨St.B, t0 ++ q :: m, c, sweepSym p :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
      simpa using A_turn p hp c (t0 ++ q :: m) r
    have h2 := B_sweep t0 ht0 c hc q m (sweepSym p :: (4 : Sym) :: (4 : Sym) :: r)
    rw [show 4 + (c :: t0).length = 4 + (t0.length + 1) by simp, iter_add, h1, h2]
    simp

/-- **The round trip.**  One complete cycle of the head between two visits to
the counter.

Hypotheses: the outward pass crosses the region block `w`, starting in the phase
given by the least significant counter digit `d` and ending in phase `q`
(`hout`); the cells beyond `w` begin with the pattern `4 2` at which the pass
turns around; the output `w'` of the pass, read from the right, is `p :: t` with
`p` a `0` or a `2` (which is what makes the pass stop there) and `t` a block of
`0`s and `2`s (which is what the return sweep can cross); and the counter
`q :: ds` is not saturated.

Conclusion: after exactly `n + (4 + t.length) + incrCost (q :: ds)` steps the
counter has been incremented, the head is back in state `A` at the left end of
the region, and the region word has become
`(t.map sweepSym).reverse ++ sweepSym p :: 4 :: 4 :: r`. -/
theorem round_trip {d q p : Sym} {ds l w w' t r : List Sym} {n : ℕ}
    (hout : Out d w q w' n) (hrev : w'.reverse = p :: t)
    (hp : p = 0 ∨ p = 2) (ht : ∀ s ∈ t, s = 0 ∨ s = 2)
    (hq : IsDigit q) (hds : ∀ s ∈ ds, IsDigit s) (hsat : ¬ Saturated (q :: ds)) :
    iter (n + (4 + t.length) + incrCost (q :: ds))
        (some (onFirst St.A (d :: (ds ++ l)) (w ++ (4 : Sym) :: (2 : Sym) :: r))) =
      some (onFirst St.A (incr (q :: ds) ++ l)
        ((t.map sweepSym).reverse ++ sweepSym p :: (4 : Sym) :: (4 : Sym) :: r)) := by
  -- the outward pass
  have h1 := out_cross hout (ds ++ l) ((4 : Sym) :: (2 : Sym) :: r)
  rw [hrev] at h1
  simp only [List.cons_append, onFirst_cons] at h1
  -- the turn and the return sweep
  have h2 := turn_and_sweep p hp t ht q (ds ++ l) r
  -- the increment
  obtain ⟨r0, r', hr⟩ : ∃ r0 r', (t.map sweepSym).reverse ++ sweepSym p :: (4 : Sym) ::
      (4 : Sym) :: r = r0 :: r' := by
    cases hrl : (t.map sweepSym).reverse with
    | nil => exact ⟨sweepSym p, (4 : Sym) :: (4 : Sym) :: r, by simp⟩
    | cons a as => exact ⟨a, as ++ sweepSym p :: (4 : Sym) :: (4 : Sym) :: r, by simp⟩
  have h3 := counter_increment q ds hq hds hsat l r' r0
  rw [iter_add, iter_add, h1, h2, hr, h3, ← hr]
  cases hrl : (t.map sweepSym).reverse ++ sweepSym p :: (4 : Sym) :: (4 : Sym) :: r with
  | nil => simp [hr] at hrl
  | cons a as =>
    rw [hrl] at hr
    cases hr
    simp [onFirst]

end TM2x5
