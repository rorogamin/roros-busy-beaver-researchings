import RequestProject.Counter

/-!
# The macroscopic rule set: outward pass, return sweep, interface

`Counter.lean` describes what happens at the two *ends* of the computation: the
base-3 counter sitting immediately to the right of the frontier `1`, and the
left-moving cascade `←A`.  This file supplies the missing middle: the exact
rules by which the head travels **out** of the counter towards the right end of
the tape and **back**.  These are the two ingredients listed as unknown in
`ANALYSIS.md` §4.5 — the interface between the counter and the region to its
right, and the structural event at the right end.

The particles involved are

* `A→` — the right-moving `A`, which crosses the region;
* `←B` — the left-moving `B`, which brings the head back and feeds the carry
  into the counter;
* `←A` — the cascade, treated in `Counter.lean`.

The main results are

* `A_on_two`, `A_on_four_three`, `A_over_two_fours` (in `Machine.lean`),
  `A_bounce`, `A_bounce_three`, `A_bounce_four`, `A_on_four_zero` — the
  complete local rule set of `A→` inside a region of `2`s and `4`s;
* `Out` and `out_cross` — the *outward pass* as an inductive relation: a
  two-phase transducer that rewrites the region as the head crosses it, with a
  theorem giving the exact number of steps and the exact resulting tape;
* `B_sweep` — the return sweep of `←B` across a block of `0`s and `2`s;
* `interface_return_increment` — **the interface rule**: the return sweep
  followed by the counter increment, in one statement;
* `right_end_extension` — **the structural event at the right end**: the head
  running into fresh tape writes `3 2`, extends the used tape by two cells and
  emits a cascade to the left.
-/

namespace TM2x5

/-- The configuration with state `st`, left tape `l` (nearest cell first) and
the head on the first cell of `xs`; cells beyond `xs` are blank. -/
def onFirst (st : St) (l : List Sym) : List Sym → Cfg
  | [] => ⟨st, l, 0, []⟩
  | x :: xs => ⟨st, l, x, xs⟩

@[simp] theorem onFirst_cons (st : St) (l : List Sym) (x : Sym) (xs : List Sym) :
    onFirst st l (x :: xs) = ⟨st, l, x, xs⟩ := rfl

@[simp] theorem onFirst_nil (st : St) (l : List Sym) :
    onFirst st l [] = ⟨st, l, 0, []⟩ := rfl

/-- The rewriting performed by the left-moving `B` on the cells it crosses:
`0 ↦ 2` and `2 ↦ 4` (`B0 → 2LB`, `B2 → 4LB`). -/
def sweepSym : Sym → Sym
  | Sym.s0 => 2
  | Sym.s2 => 4
  | s => s

/-! ## The local rules of the right-moving `A`

The head in state `A` moving right meets a cell `x`; the table entries
`A2 → 3RA`, `A4 → 2RB`, `A3 → 2LA`, `A0 → 1RB` give the complete list of
possibilities.  Only the cells `2` and `4` keep the head moving right; a `3`
turns it into a cascade, a `0` is fresh tape and a `1` halts the machine. -/

/-- `A→` crossing a `2` writes a `3`. -/
theorem A_on_two (c : Sym) (l r : List Sym) :
    iter 1 (some ⟨St.A, l, 2, c :: r⟩) = some ⟨St.A, (3 : Sym) :: l, c, r⟩ := rfl

/-- `A→` crossing `4 3` writes `2 4` (`A4 → 2RB`, `B3 → 4RA`). -/
theorem A_on_four_three (c : Sym) (l r : List Sym) :
    iter 2 (some ⟨St.A, l, 4, (3 : Sym) :: c :: r⟩) =
      some ⟨St.A, (4 : Sym) :: (2 : Sym) :: l, c, r⟩ := rfl

/-- **The bounce.**  `A→` meeting `4 2` writes `2 4`, turns around, rewrites the
`2` it has just written as a `4`, and arrives as a left-moving `B` on the cell
to the left of where it started — whatever that cell contains.  Three steps. -/
theorem A_bounce (p : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, p :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.B, l, p, (4 : Sym) :: (4 : Sym) :: r⟩ := rfl

/-- After the bounce, a `3` on the left sends the head right again: the three
cells `3 4 2` end up as `4 2 0`, six steps in all. -/
theorem A_bounce_three (c : Sym) (l r : List Sym) :
    iter 6 (some ⟨St.A, (3 : Sym) :: l, 4, (2 : Sym) :: c :: r⟩) =
      some ⟨St.A, (0 : Sym) :: (2 : Sym) :: (4 : Sym) :: l, c, r⟩ := rfl

/-- After the bounce, a `4` on the left also sends the head right again: the
three cells `4 4 2` end up as `0 2 0`, six steps in all. -/
theorem A_bounce_four (c : Sym) (l r : List Sym) :
    iter 6 (some ⟨St.A, (4 : Sym) :: l, 4, (2 : Sym) :: c :: r⟩) =
      some ⟨St.A, (0 : Sym) :: (2 : Sym) :: (0 : Sym) :: l, c, r⟩ := rfl

/-- **The turn.**  After the bounce, a `0` or a `2` on the left does *not* send
the head back to the right: the left-moving `B` rewrites it (`0 ↦ 2`, `2 ↦ 4`)
and keeps going, so the outward pass is over.  Together with `A_bounce_three`
and `A_bounce_four` this exhausts the possibilities, so the pass stops exactly
at the first `4 2` that is preceded by a `0` or a `2`. -/
theorem A_turn (p : Sym) (hp : p = 0 ∨ p = 2) (a : Sym) (l r : List Sym) :
    iter 4 (some ⟨St.A, p :: a :: l, 4, (2 : Sym) :: r⟩) =
      some ⟨St.B, l, a, sweepSym p :: (4 : Sym) :: (4 : Sym) :: r⟩ := by
  rcases hp with h | h <;> subst h <;> rfl

/-- `A→` meeting `4 0` also turns the head around, after three steps. -/
theorem A_on_four_zero (p : Sym) (l r : List Sym) :
    iter 3 (some ⟨St.A, p :: l, 4, (0 : Sym) :: r⟩) =
      some ⟨St.B, l, p, (4 : Sym) :: (2 : Sym) :: r⟩ := rfl

/-! ## The outward pass

Putting the local rules together, the head crossing a block of `2`s and `4`s
behaves as a transducer with two phases, recorded in the symbol `p` sitting
immediately to the left of the head: `p = 3` (the head has just consumed a `2`)
and `p = 0` (the head has just consumed a pair `4 4`, or has just completed a
bounce).  The pattern `4 2` is crossed in phase `3` and in phase `4`, but
*stops* the pass in phase `0` — and phase `0` is the phase left behind by every
pair `4 4`.

`Out p w q w' n` means: the head, in state `A`, standing on the first cell of
the block `w`, with the cell to its left holding `p`, crosses the whole of `w`
in exactly `n` steps, leaving `w'` in place of `w`, the cell to the left holding
`q`, and the head in state `A` on the cell just beyond `w`. -/
inductive Out : Sym → List Sym → Sym → List Sym → ℕ → Prop
  /-- The empty block is crossed in no steps. -/
  | nil (p : Sym) : Out p [] p [] 0
  /-- A `2` is rewritten as a `3`; the head enters phase `3`.  (That `3` may
  later be rewritten as a `4` by a bounce, which is why the rest of the pass
  reports the symbol `q` that the cell finally holds.) -/
  | two {p q : Sym} {w w' : List Sym} {n : ℕ} :
      Out 3 w q w' n → Out p (2 :: w) p (q :: w') (n + 1)
  /-- `4 3 ↦ 2 4`, entering phase `4`. -/
  | four_three {p q : Sym} {w w' : List Sym} {n : ℕ} :
      Out 4 w q w' n → Out p (4 :: 3 :: w) p ((2 : Sym) :: q :: w') (n + 2)
  /-- `4 4 ↦ 2 0`, entering phase `0`. -/
  | four_four {p q : Sym} {w w' : List Sym} {n : ℕ} :
      Out 0 w q w' n → Out p (4 :: 4 :: w) p ((2 : Sym) :: q :: w') (n + 2)
  /-- `3 | 4 2 ↦ 4 | 2 0`, a bounce off the `3` on the left, entering phase
  `0`. -/
  | four_two_of_three {q : Sym} {w w' : List Sym} {n : ℕ} :
      Out 0 w q w' n → Out 3 (4 :: 2 :: w) 4 ((2 : Sym) :: q :: w') (n + 6)
  /-- `4 | 4 2 ↦ 0 | 2 0`, a bounce off the `4` on the left, entering phase
  `0`. -/
  | four_two_of_four {q : Sym} {w w' : List Sym} {n : ℕ} :
      Out 0 w q w' n → Out 4 (4 :: 2 :: w) 0 ((2 : Sym) :: q :: w') (n + 6)

/-! The four local rules again, in the form in which the induction below uses
them: the tape beyond the cells being rewritten is an arbitrary list, possibly
empty (in which case the head lands on fresh blank tape). -/

theorem step_A_two (l xs : List Sym) :
    iter 1 (some ⟨St.A, l, 2, xs⟩) = some (onFirst St.A ((3 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_A_four_three (l xs : List Sym) :
    iter 2 (some ⟨St.A, l, 4, (3 : Sym) :: xs⟩) =
      some (onFirst St.A ((4 : Sym) :: (2 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_A_four_four (l xs : List Sym) :
    iter 2 (some ⟨St.A, l, 4, (4 : Sym) :: xs⟩) =
      some (onFirst St.A ((0 : Sym) :: (2 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_A_bounce_three (l xs : List Sym) :
    iter 6 (some ⟨St.A, (3 : Sym) :: l, 4, (2 : Sym) :: xs⟩) =
      some (onFirst St.A ((0 : Sym) :: (2 : Sym) :: (4 : Sym) :: l) xs) := by
  cases xs <;> rfl

theorem step_A_bounce_four (l xs : List Sym) :
    iter 6 (some ⟨St.A, (4 : Sym) :: l, 4, (2 : Sym) :: xs⟩) =
      some (onFirst St.A ((0 : Sym) :: (2 : Sym) :: (0 : Sym) :: l) xs) := by
  cases xs <;> rfl

/-- **The outward pass.**  Every derivation of `Out p w q w' n` is a genuine run
of the machine: from the head standing on the first cell of `w` in state `A`,
with `p` to its left and an arbitrary tape `r` beyond `w`, the machine takes
exactly `n` steps and arrives at the first cell of `r`, in state `A`, having
rewritten `w` as `w'` and `p` as `q`. -/
theorem out_cross {p q : Sym} {w w' : List Sym} {n : ℕ} (h : Out p w q w' n) :
    ∀ l r : List Sym,
      iter n (some (onFirst St.A (p :: l) (w ++ r))) =
        some (onFirst St.A (w'.reverse ++ q :: l) r) := by
  induction h with
  | nil p => intro l r; simp [iter]
  | @two p q w w' n _ ih =>
    intro l r
    rw [show n + 1 = 1 + n by omega, iter_add]
    simp only [List.cons_append, onFirst_cons]
    rw [step_A_two, ih (p :: l) r]
    simp
  | @four_three p q w w' n _ ih =>
    intro l r
    rw [show n + 2 = 2 + n by omega, iter_add]
    simp only [List.cons_append, onFirst_cons]
    rw [step_A_four_three, ih (2 :: p :: l) r]
    simp
  | @four_four p q w w' n _ ih =>
    intro l r
    rw [show n + 2 = 2 + n by omega, iter_add]
    simp only [List.cons_append, onFirst_cons]
    rw [step_A_four_four, ih (2 :: p :: l) r]
    simp
  | @four_two_of_three q w w' n _ ih =>
    intro l r
    rw [show n + 6 = 6 + n by omega, iter_add]
    simp only [List.cons_append, onFirst_cons]
    rw [step_A_bounce_three, ih (2 :: 4 :: l) r]
    simp
  | @four_two_of_four q w w' n _ ih =>
    intro l r
    rw [show n + 6 = 6 + n by omega, iter_add]
    simp only [List.cons_append, onFirst_cons]
    rw [step_A_bounce_four, ih (2 :: 0 :: l) r]
    simp

/-! ## The return sweep -/

/-- **The return sweep.**  A left-moving `B` crossing a block of cells each
holding `0` or `2` rewrites them (`0 ↦ 2`, `2 ↦ 4`) at one step per cell and
stops on the first cell that holds something else. -/
theorem B_sweep : ∀ (w : List Sym), (∀ s ∈ w, s = 0 ∨ s = 2) → ∀ (c : Sym),
    (c = 0 ∨ c = 2) → ∀ (a : Sym) (l r : List Sym),
    iter (w.length + 1) (some ⟨St.B, w ++ a :: l, c, r⟩) =
      some ⟨St.B, l, a, (w.map sweepSym).reverse ++ sweepSym c :: r⟩ := by
  intro w
  induction w with
  | nil =>
    intro _ c hc a l r
    rcases hc with h | h <;> subst h <;> rfl
  | cons x w ih =>
    intro hw c hc a l r
    have hx : x = 0 ∨ x = 2 := hw x (List.mem_cons_self ..)
    have hw' : ∀ s ∈ w, s = 0 ∨ s = 2 := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    have h1 : iter 1 (some (⟨St.B, (x :: w) ++ a :: l, c, r⟩ : Cfg)) =
        some ⟨St.B, w ++ a :: l, x, sweepSym c :: r⟩ := by
      rcases hc with h | h <;> subst h <;> rfl
    rw [show (x :: w).length + 1 = 1 + (w.length + 1) by simp; omega, iter_add, h1,
      ih hw' x hx a l (sweepSym c :: r)]
    simp

/-! ## The interface between the region and the counter -/

/-- **The interface rule.**  The head coming back from the right as a left-moving
`B` across a block `w ++ [b]` of cells holding `0`s and `2`s reaches the least
significant digit of the counter and increments it: after
`w.length + 2 + incrCost (d :: ds)` steps the counter word `d :: ds` has been
replaced by its increment and the head is on its way out again, in state `A`,
standing on the cell `sweepSym b` next to the counter.

This is the exact hand-over rule between the two halves of the tape that
`ANALYSIS.md` §4.5 listed as missing.  Note that there is no change of digit
packing: the counter is one cell per digit throughout, and the cells of the
transition zone are not counter digits at all — they are the `0`/`2` cells that
the sweep converts to `2`/`4`. -/
theorem interface_return_increment (w : List Sym) (hw : ∀ s ∈ w, s = 0 ∨ s = 2)
    (b c : Sym) (hb : b = 0 ∨ b = 2) (hc : c = 0 ∨ c = 2)
    (d : Sym) (ds : List Sym) (hd : IsDigit d) (hds : ∀ s ∈ ds, IsDigit s)
    (hsat : ¬ Saturated (d :: ds)) (l r : List Sym) :
    iter (w.length + 2 + incrCost (d :: ds))
        (some ⟨St.B, w ++ b :: d :: ds ++ l, c, r⟩) =
      some ⟨St.A, incr (d :: ds) ++ l, sweepSym b,
              (w.map sweepSym).reverse ++ sweepSym c :: r⟩ := by
  have hwb : ∀ s ∈ w ++ [b], s = 0 ∨ s = 2 := by
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact hw s h
    · simpa [List.mem_singleton] using (List.mem_singleton.mp h) ▸ hb
  have hsplit : (w ++ [b]) ++ d :: (ds ++ l) = w ++ b :: d :: ds ++ l := by simp
  have h1 := B_sweep (w ++ [b]) hwb c hc d (ds ++ l) r
  rw [hsplit] at h1
  have hlen : (w ++ [b]).length + 1 = w.length + 2 := by simp
  rw [hlen] at h1
  have hmap : ((w ++ [b]).map sweepSym).reverse ++ sweepSym c :: r =
      sweepSym b :: ((w.map sweepSym).reverse ++ sweepSym c :: r) := by simp
  rw [hmap] at h1
  rw [iter_add, h1,
    counter_increment d ds hd hds hsat l ((w.map sweepSym).reverse ++ sweepSym c :: r)
      (sweepSym b)]

/-! ## The structural event at the right end -/


/-- **Extension of the used tape.**  When the outward pass runs off the right
end of the used tape, the head writes `3 2`, the used tape grows by two cells
and a cascade `←A` leaves to the left in mode `Q`.  (Three steps: `A0 → 1RB`,
`B0 → 2LB`, `B1 → 3LA`.) -/
theorem right_end_extension (a : Sym) (l : List Sym) :
    iter 3 (some ⟨St.A, a :: l, 0, []⟩) =
      some ⟨St.A, l, a, (3 : Sym) :: (2 : Sym) :: []⟩ := rfl

/-! ## Closing the loop: the cascade re-crosses what the pass has just written

The outward pass and the cascade travel over the *same* cells, in opposite
directions and one immediately after the other.  This is what makes the halting
question a question about the pass: the cascade born at the right end meets
exactly the word the pass has just left behind.

The pass writes a `3` for each `2` it consumes and a pair `2 0` for each pair
`4 4`; it writes a `4` only through the rules `four_three` and
`four_two_of_three`.  A `4` stops the cascade dead (`cascade_P_four_stops`,
`cascade_Q_four_stops`), whereas a word made of `3`s and `2 0` pairs is crossed
completely — that is `cross_passRev` below.  So the machine halts exactly when
some outward pass reaches fresh tape leaving no `4` behind (and the remaining
cells between the region and the frontier are crossable as well). -/

/-- Words left behind by a `4`-free outward pass, listed in the order in which
the returning cascade meets them (nearest cell first): a `3` for each `2` the
pass consumed, and a pair `0 2` for each pair `4 4`. -/
inductive PassRev : List Sym → Prop
  | nil : PassRev []
  | three {u : List Sym} : PassRev u → PassRev ((3 : Sym) :: u)
  | zero_two {u : List Sym} : PassRev u → PassRev ((0 : Sym) :: (2 : Sym) :: u)

/-- `CrossL m xs` is `Cross m` applied to the head and the tail of `xs`; the
empty list is crossed vacuously (the cascade never gets there). -/
def CrossL (m : Mode) : List Sym → Prop
  | [] => True
  | x :: xs => Cross m x xs

theorem crossL_cons {m : Mode} {x : Sym} {xs : List Sym} :
    CrossL m (x :: xs) ↔ Cross m x xs := Iff.rfl

theorem crossL_append_cons {m : Mode} (u : List Sym) (c : Sym) (w : List Sym) :
    ∃ x xs, u ++ c :: w = x :: xs ∧ (CrossL m (u ++ c :: w) ↔ Cross m x xs) := by
  cases u with
  | nil => exact ⟨c, w, rfl, Iff.rfl⟩
  | cons y ys => exact ⟨y, ys ++ c :: w, rfl, Iff.rfl⟩

/-- **A `4`-free pass output is always crossed.**  If the cascade, in mode `P`,
can cross the tape starting at the cell `c`, then it can also cross any word
left behind by a `4`-free outward pass placed in front of it. -/
theorem cross_passRev {u : List Sym} (h : PassRev u) (c : Sym) (w : List Sym)
    (hc : Cross Mode.P c w) : CrossL Mode.P (u ++ c :: w) := by
  induction h with
  | nil => exact hc
  | @three u _ ih =>
    obtain ⟨x, xs, hx, hiff⟩ := crossL_append_cons (m := Mode.P) u c w
    have : Cross Mode.P x xs := hiff.mp ih
    show Cross Mode.P 3 (u ++ c :: w)
    rw [hx]
    exact Cross.P3 this
  | @zero_two u _ ih =>
    obtain ⟨x, xs, hx, hiff⟩ := crossL_append_cons (m := Mode.P) u c w
    have hP : Cross Mode.P x xs := hiff.mp ih
    show Cross Mode.P 0 ((2 : Sym) :: (u ++ c :: w))
    refine Cross.P0 ?_
    rw [hx]
    exact Cross.Q2 hP

/-- **The end-to-end halting rule.**  Suppose the head starts an outward pass at
the left end of the region `w` (state `A`, the cell `p` to its left), the pass
crosses the whole of `w` and runs into fresh tape, and the word it leaves
behind, read from the right, starts with a `3` and is followed by cells that the
cascade can cross all the way to the frontier.  Then the machine halts.

This is the exact composition of the three macroscopic events: outward pass
(`out_cross`), extension of the tape at the right end (`right_end_extension`),
and the returning cascade (`cross_halts`). -/
theorem pass_then_cascade_halts {p q : Sym} {w w' v : List Sym} {n : ℕ}
    (h : Out p w q w' n) (hw' : w' = v ++ [(3 : Sym)]) (l : List Sym)
    (hcross : CrossL Mode.P (v.reverse ++ q :: l)) :
    ∃ N, iter N (some (onFirst St.A (p :: l) w)) = none := by
  obtain ⟨x, xs, hx, hiff⟩ := crossL_append_cons (m := Mode.P) v.reverse q l
  have hP : Cross Mode.P x xs := hiff.mp hcross
  have hQ : Cross Mode.Q 3 (v.reverse ++ q :: l) := by rw [hx]; exact Cross.Q3 hP
  obtain ⟨k, hk⟩ := cross_halts hQ [] [(2 : Sym)]
  have hout := out_cross h l []
  simp only [List.append_nil] at hout
  have h2 : onFirst St.A (w'.reverse ++ q :: l) [] =
      (⟨St.A, (3 : Sym) :: (v.reverse ++ q :: l), 0, []⟩ : Cfg) := by
    simp [hw', onFirst]
  refine ⟨n + 3 + k, ?_⟩
  rw [iter_add, iter_add, hout, h2, right_end_extension]
  simpa [Mode.sym] using hk

/-- **The halting criterion in terms of the pass alone.**  If an outward pass
reaches fresh tape leaving a `4`-free word behind (a `3` at the right end and
`3`s and `2 0` pairs before it), and the cell `q` just left of the region starts
a crossable block, then the machine halts. -/
theorem halt_of_four_free_pass {p q : Sym} {w w' v : List Sym} {n : ℕ}
    (h : Out p w q w' n) (hw' : w' = v ++ [(3 : Sym)]) (hv : PassRev v.reverse)
    (l : List Sym) (hq : Cross Mode.P q l) :
    ∃ N, iter N (some (onFirst St.A (p :: l) w)) = none :=
  pass_then_cascade_halts h hw' l (cross_passRev hv q l hq)

/-! ### The second way a cascade is born: the pass runs onto a `3`

The pass has no rule for a cell holding `3`: there `A3 → 2LA` turns the head
around and a cascade leaves to the left, this time in mode `P` (the cell to its
right now holds `2`).  Again the cascade immediately re-crosses the output of
the pass that produced it. -/

/-- **Mid-tape cascade.**  If the outward pass over `w` is followed by a cell
holding `3`, a mode-`P` cascade starts on the last cell the pass has written; if
that cascade crosses the pass output and the cells beyond, the machine halts. -/
theorem pass_then_mid_cascade_halts {p q a : Sym} {w w' v : List Sym} {n : ℕ}
    (h : Out p w q w' n) (hw' : w' = v ++ [a]) (l r : List Sym)
    (hcross : Cross Mode.P a (v.reverse ++ q :: l)) :
    ∃ N, iter N (some (onFirst St.A (p :: l) (w ++ (3 : Sym) :: r))) = none := by
  obtain ⟨k, hk⟩ := cross_halts hcross [] r
  have hout := out_cross h l ((3 : Sym) :: r)
  have h2 : onFirst St.A (w'.reverse ++ q :: l) ((3 : Sym) :: r) =
      (⟨St.A, a :: (v.reverse ++ q :: l), 3, r⟩ : Cfg) := by
    simp [hw', onFirst]
  refine ⟨n + 1 + k, ?_⟩
  rw [iter_add, iter_add, hout, h2]
  have h3 : iter 1 (some (⟨St.A, a :: (v.reverse ++ q :: l), 3, r⟩ : Cfg)) =
      some ⟨St.A, v.reverse ++ q :: l, a, (2 : Sym) :: r⟩ := rfl
  rw [h3]
  simpa [Mode.sym] using hk

/-- The `4`-free form of the previous theorem: a pass whose output is made of
`3`s and `2 0` pairs only, followed by a `3`, halts the machine as soon as the
cells beyond the region are crossable. -/
theorem halt_of_four_free_pass_mid {p q : Sym} {w w' : List Sym} {n : ℕ}
    (h : Out p w q w' n) (hv : PassRev w'.reverse) (l r : List Sym)
    (hq : Cross Mode.P q l) :
    ∃ N, iter N (some (onFirst St.A (p :: l) (w ++ (3 : Sym) :: r))) = none := by
  have hcl := cross_passRev hv q l hq
  cases hw : w'.reverse with
  | nil =>
    -- the pass wrote nothing, so the cascade starts on the cell `q` itself
    obtain ⟨k, hk⟩ := cross_halts hq [] r
    have hw'nil : w' = [] := by simpa using congrArg List.reverse hw
    have hout := out_cross h l ((3 : Sym) :: r)
    have h2 : onFirst St.A (w'.reverse ++ q :: l) ((3 : Sym) :: r) =
        (⟨St.A, q :: l, 3, r⟩ : Cfg) := by simp [hw'nil, onFirst]
    refine ⟨n + 1 + k, ?_⟩
    rw [iter_add, iter_add, hout, h2]
    have h3 : iter 1 (some (⟨St.A, q :: l, 3, r⟩ : Cfg)) =
        some ⟨St.A, l, q, (2 : Sym) :: r⟩ := rfl
    rw [h3]
    simpa [Mode.sym] using hk
  | cons a u =>
    have hw' : w' = u.reverse ++ [a] := by
      have := congrArg List.reverse hw
      simpa using this
    refine pass_then_mid_cascade_halts h hw' l r ?_
    have : Cross Mode.P a (u ++ q :: l) := by
      rw [hw] at hcl
      exact hcl
    simpa using this

/-- A worked instance, showing that the criterion is not vacuous: the frontier
`1`, then two cells holding `2`, then fresh tape.  The pass rewrites `2 2` as
`3 3`, the tape is extended, and the cascade crosses the two `3`s and halts the
machine. -/
theorem halt_of_frontier_two_twos (l : List Sym) :
    ∃ N, iter N (some (⟨St.A, (1 : Sym) :: l, 2, [(2 : Sym)]⟩ : Cfg)) = none := by
  have hout : Out 1 [(2 : Sym), (2 : Sym)] 1 [(3 : Sym), (3 : Sym)] 2 :=
    Out.two (Out.two (Out.nil 3))
  have h := halt_of_four_free_pass hout (v := [(3 : Sym)]) rfl
    (by simpa using PassRev.three PassRev.nil) l Cross.haltP
  simpa [onFirst] using h

/-- The same worked instance for a mid-tape cascade: frontier `1`, two cells
holding `2`, then a cell holding `3`.  The pass rewrites `2 2` as `3 3`, the `3`
turns the head around, and the mode-`P` cascade crosses the two `3`s and halts
the machine. -/
theorem halt_of_frontier_two_twos_mid (l r : List Sym) :
    ∃ N, iter N (some (⟨St.A, (1 : Sym) :: l, 2, (2 : Sym) :: (3 : Sym) :: r⟩ : Cfg))
      = none := by
  have hout : Out 1 [(2 : Sym), (2 : Sym)] 1 [(3 : Sym), (3 : Sym)] 2 :=
    Out.two (Out.two (Out.nil 3))
  have h := halt_of_four_free_pass_mid hout
    (by simpa using PassRev.three (PassRev.three PassRev.nil)) l r Cross.haltP
  simpa [onFirst] using h

end TM2x5
