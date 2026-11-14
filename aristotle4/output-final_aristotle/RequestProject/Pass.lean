import RequestProject.Binary

/-!
# The outward pass as a total function of the tape

`Macro.lean` describes the outward pass by the inductive relation `Out`, which
covers only the case in which the head crosses a given block completely, and
`Binary.lean` isolates the two events that happen at a *marker* (a cell holding
`3`).  `ANALYSIS.md` §6.3 lists as the first missing item the **coverage**
statement: which of the local rules applies at a given moment is a function of
the shape of the tape to the right of the head, and that function was not
available.

This file supplies it.  `passF p w` is a total, computable function of

* the **phase** `p` — the symbol in the cell immediately to the left of the
  head, which is what decides the behaviour at the pattern `4 2`; and
* the tape `w` to the right of the head (cells beyond `w` are blank),

and it returns the complete description of the pass: how it ends, how many steps
it takes, and the exact tape it leaves behind.  `passF_correct` proves that the
machine really does what `passF` says.

There are exactly four ways an outward pass can end (`PassEnd`):

* `turn`     — a `4 2` met in phase `0` or `2`: the head turns and comes back as
               a left-moving `B` (this is the common case; `Macro.A_turn`);
* `turnZero` — a `4` met at the right edge of the used tape: same, three steps
               (`Macro.A_on_four_zero`);
* `mark`     — the head runs onto a cell holding `3` and a mode-`P` cascade is
               born (`A3 → 2LA`);
* `fresh`    — the head runs off the right end of the used tape, which is
               extended by two cells, and a mode-`Q` cascade is born
               (`Macro.right_end_extension`).

plus the halting case (the head runs onto a `1`) and the residual case `other`,
which collects the finitely many configurations that a pass never produces in
this machine (a `0` in the middle of the region, a `4 1`, and a pass entering
the pattern `4 2` from the frontier symbol `1`).
-/

namespace TM2x5

/-- The configuration whose head sits on the **first cell of the left list**
`L` (nearest cell first), with `R` the tape to the right of the head; `L = []`
means the head is on a blank cell with nothing but blanks to its left.  This is
the mirror image of `onFirst`, and it is what the rules that turn the head
around produce. -/
def cfgAt (st : St) : List Sym → List Sym → Cfg
  | [], R => ⟨st, [], 0, R⟩
  | a :: L, R => ⟨st, L, a, R⟩

@[simp] theorem cfgAt_cons (st : St) (a : Sym) (L R : List Sym) :
    cfgAt st (a :: L) R = ⟨st, L, a, R⟩ := rfl

@[simp] theorem cfgAt_nil (st : St) (R : List Sym) :
    cfgAt st [] R = ⟨st, [], 0, R⟩ := rfl

/-- The four ways an outward pass can end. -/
inductive PassEnd
  | turn
  | turnZero
  | mark
  | fresh
  deriving DecidableEq, Repr

/-- The state the head is in when the pass ends: after a turn it is a
left-moving `B`, after a cascade birth it is a left-moving `A`. -/
def PassEnd.st : PassEnd → St
  | PassEnd.turn => St.B
  | PassEnd.turnZero => St.B
  | PassEnd.mark => St.A
  | PassEnd.fresh => St.A

/-- The result of an outward pass: either it stops (`stop e L R n`: after `n`
steps the head is on the first cell of `L` — the rewritten tape to its left,
nearest cell first — in the state belonging to `e`, with `R` to its right), or
the machine halts, or the situation is one of the finitely many that this
machine never produces. -/
inductive PassRes
  | stop (e : PassEnd) (L R : List Sym) (n : ℕ)
  | halt (n : ℕ)
  | other
  deriving DecidableEq, Repr

/-- Prepend the cells `x` (in tape order) that the enclosing rule has rewritten,
and charge its `k` steps. -/
def PassRes.extend (x : List Sym) (k : ℕ) : PassRes → PassRes
  | PassRes.stop e L R n => PassRes.stop e (x ++ L) R (n + k)
  | PassRes.halt n => PassRes.halt (n + k)
  | PassRes.other => PassRes.other

/-- **The outward pass.**  `passF p w` runs the head, in state `A`, across the
tape `w` to its right (blanks beyond `w`), the cell to its left holding `p`.
The returned word `L` lists, in tape order starting at the cell holding `p`, the
final contents of the cells the pass has rewritten; in the `turn` case the cell
the head comes to rest on is not part of `L` but of `R`, because the head sweeps
back over it. -/
def passF : Sym → List Sym → PassRes
  | p, [] => PassRes.stop PassEnd.fresh [p] [3, 2] 3
  | p, [Sym.s0] => PassRes.stop PassEnd.fresh [p] [3, 2] 3
  | _, Sym.s1 :: _ => PassRes.halt 1
  | p, Sym.s3 :: w => PassRes.stop PassEnd.mark [p] (2 :: w) 1
  | p, Sym.s2 :: w => (passF 3 w).extend [p] 1
  | p, [Sym.s4] => PassRes.stop PassEnd.turnZero [p] [4, 2] 3
  | p, Sym.s4 :: Sym.s0 :: w => PassRes.stop PassEnd.turnZero [p] (4 :: 2 :: w) 3
  | p, Sym.s4 :: Sym.s3 :: w => (passF 4 w).extend [p, 2] 2
  | p, Sym.s4 :: Sym.s4 :: w => (passF 0 w).extend [p, 2] 2
  | Sym.s3, Sym.s4 :: Sym.s2 :: w => (passF 0 w).extend [4, 2] 6
  | Sym.s4, Sym.s4 :: Sym.s2 :: w => (passF 0 w).extend [0, 2] 6
  | Sym.s0, Sym.s4 :: Sym.s2 :: w => PassRes.stop PassEnd.turn [] (2 :: 4 :: 4 :: w) 4
  | Sym.s2, Sym.s4 :: Sym.s2 :: w => PassRes.stop PassEnd.turn [] (4 :: 4 :: 4 :: w) 4
  | _, Sym.s4 :: Sym.s2 :: _ => PassRes.other
  | _, Sym.s4 :: Sym.s1 :: _ => PassRes.other
  | _, Sym.s0 :: _ => PassRes.other
  termination_by _ w => w.length

/-- What `passF p w` claims about the machine: starting in state `A` on the
first cell of `w`, with `p` immediately to the left and the tape `l` beyond
that. -/
def PassClaim (p : Sym) (w l : List Sym) : PassRes → Prop
  | PassRes.stop e L R n =>
      iter n (some (onFirst St.A (p :: l) w)) = some (cfgAt e.st (L.reverse ++ l) R)
  | PassRes.halt n => iter n (some (onFirst St.A (p :: l) w)) = none
  | PassRes.other => True

/-- The inductive step: if the first `k` steps carry the pass from its starting
configuration to the starting configuration of the recursive call, and the
rewritten cells `x` account for the difference between the two left tapes, then
the claim for the recursive call implies the claim for the whole. -/
theorem claim_extend {p p' : Sym} {w w' l l' x : List Sym} {k : ℕ} {res : PassRes}
    (hstart : iter k (some (onFirst St.A (p :: l) w)) = some (onFirst St.A (p' :: l') w'))
    (hx : x.reverse ++ l = l')
    (hres : PassClaim p' w' l' res) :
    PassClaim p w l (res.extend x k) := by
  cases res with
  | stop e L R n =>
    show iter (n + k) _ = _
    rw [Nat.add_comm, iter_add, hstart]
    rw [PassClaim] at hres
    rw [hres]
    simp [← hx]
  | halt n =>
    show iter (n + k) _ = _
    rw [Nat.add_comm, iter_add, hstart]
    exact hres
  | other => trivial

/-- The turn, in the form in which the pass function needs it: the head may
end up on a blank cell if the tape to the left is exhausted. -/
theorem A_turn_gen (p : Sym) (hp : p = 0 ∨ p = 2) (l r : List Sym) :
    iter 4 (some ⟨St.A, p :: l, 4, (2 : Sym) :: r⟩) =
      some (cfgAt St.B l (sweepSym p :: (4 : Sym) :: (4 : Sym) :: r)) := by
  cases l <;> rcases hp with h | h <;> subst h <;> rfl

/-- **Correctness of the pass function.**  Whatever the phase and the tape, the
machine does exactly what `passF` says. -/
theorem passF_correct : ∀ (p : Sym) (w : List Sym), ∀ l : List Sym,
    PassClaim p w l (passF p w) := by
  intro p w
  induction p, w using passF.induct with
  | case1 p => intro l; simp only [passF]; exact rfl
  | case2 p => intro l; simp only [passF]; exact rfl
  | case3 p w => intro l; simp only [passF]; exact rfl
  | case4 p w => intro l; simp only [passF]; exact rfl
  | case5 p w ih =>
    intro l
    simp only [passF]
    refine claim_extend (p' := 3) (w' := w) (l' := p :: l) (x := [p]) ?_ (by simp) (ih (p :: l))
    exact step_A_two (p :: l) w
  | case6 p => intro l; simp only [passF]; exact rfl
  | case7 p w => intro l; simp only [passF]; exact rfl
  | case8 p w ih =>
    intro l
    simp only [passF]
    refine claim_extend (p' := 4) (w' := w) (l' := 2 :: p :: l) (x := [p, 2]) ?_ (by simp)
      (ih (2 :: p :: l))
    exact step_A_four_three (p :: l) w
  | case9 p w ih =>
    intro l
    simp only [passF]
    refine claim_extend (p' := 0) (w' := w) (l' := 2 :: p :: l) (x := [p, 2]) ?_ (by simp)
      (ih (2 :: p :: l))
    exact step_A_four_four (p :: l) w
  | case10 w ih =>
    intro l
    simp only [passF]
    refine claim_extend (p' := 0) (w' := w) (l' := 2 :: 4 :: l) (x := [4, 2]) ?_ (by simp)
      (ih (2 :: 4 :: l))
    exact step_A_bounce_three l w
  | case11 w ih =>
    intro l
    simp only [passF]
    refine claim_extend (p' := 0) (w' := w) (l' := 2 :: 0 :: l) (x := [0, 2]) ?_ (by simp)
      (ih (2 :: 0 :: l))
    exact step_A_bounce_four l w
  | case12 w =>
    intro l
    simp only [passF]
    simpa [PassClaim, PassEnd.st] using A_turn_gen 0 (Or.inl rfl) l w
  | case13 w =>
    intro l
    simp only [passF]
    simpa [PassClaim, PassEnd.st] using A_turn_gen 2 (Or.inr rfl) l w
  | case14 p w h1 h2 _ _ => intro l; simp only [passF]; exact trivial
  | case15 p w => intro l; simp only [passF]; exact trivial
  | case16 p w h => intro l; simp only [passF]; exact trivial

/-! ## The residual case never happens

`passF` is total, but three of its branches return `other`, i.e. make no claim:
a `0` in the middle of the region, the pattern `4 1`, and the pattern `4 2`
entered with the frontier symbol `1` as phase.  None of them is a pass: a pass
runs over cells holding `2`, `3` or `4` and its phase is a counter digit or a
cell it has just written, never a `1`. -/

@[simp] theorem extend_eq_other_iff (x : List Sym) (k : ℕ) (res : PassRes) :
    res.extend x k = PassRes.other ↔ res = PassRes.other := by
  cases res <;> simp [PassRes.extend]

/-- **Coverage.**  On a region made of the symbols `2`, `3` and `4`, entered
with any phase other than the frontier symbol `1`, the pass function always
returns a definite answer: the rules of `Macro.lean` and `Binary.lean` cover
every outward pass. -/
theorem passF_ne_other : ∀ (p : Sym) (w : List Sym), p ≠ 1 →
    (∀ s ∈ w, s = 2 ∨ s = 3 ∨ s = 4) → passF p w ≠ PassRes.other := by
  intro p w
  induction p, w using passF.induct with
  | case1 p => intro _ _; simp [passF]
  | case2 p => intro _ _; simp [passF]
  | case3 p w => intro _ _; simp [passF]
  | case4 p w => intro _ _; simp [passF]
  | case5 p w ih =>
    intro _ hw
    simp only [passF, ne_eq, extend_eq_other_iff]
    exact ih (by decide) fun s hs => hw s (List.mem_cons_of_mem _ hs)
  | case6 p => intro _ _; simp [passF]
  | case7 p w =>
    intro _ hw
    rcases hw Sym.s0 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with h | h | h <;>
      exact absurd h (by decide)
  | case8 p w ih =>
    intro _ hw
    simp only [passF, ne_eq, extend_eq_other_iff]
    exact ih (by decide) fun s hs =>
      hw s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  | case9 p w ih =>
    intro _ hw
    simp only [passF, ne_eq, extend_eq_other_iff]
    exact ih (by decide) fun s hs =>
      hw s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  | case10 w ih =>
    intro _ hw
    simp only [passF, ne_eq, extend_eq_other_iff]
    exact ih (by decide) fun s hs =>
      hw s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  | case11 w ih =>
    intro _ hw
    simp only [passF, ne_eq, extend_eq_other_iff]
    exact ih (by decide) fun s hs =>
      hw s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  | case12 w => intro _ _; simp [passF]
  | case13 w => intro _ _; simp [passF]
  | case14 p w h3 h4 h0 h2 =>
    intro hp _
    refine absurd ?_ hp
    cases p
    · exact absurd rfl h0
    · rfl
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
  | case15 p w =>
    intro _ hw
    rcases hw Sym.s1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with h | h | h <;>
      exact absurd h (by decide)
  | case16 p w h =>
    intro _ hw
    rcases hw Sym.s0 (List.mem_cons_self ..) with h | h | h <;> exact absurd h (by decide)

/-! ## Marker events

The commonest event of the computation is the returning sweep meeting a cell
holding `3` (a *marker* left behind by an earlier pass).  The step `B3 → 4RA`
turns the marker into a `4` and launches an outward pass in phase `4`, so a
marker event is nothing but a pass with one extra step in front of it — and
`passF` therefore classifies marker events completely.  `Binary.marker_increment`
and `Binary.marker_shift` are the two cases that occur when the region is in
binary-counter shape. -/

/-- The marker event: one step, then an outward pass in phase `4`. -/
def markerF (w : List Sym) : PassRes := (passF 4 w).extend [] 1

/-- What `markerF` claims, for a head sweeping left in state `B` that has just
arrived on a marker, with `l` to its left and `w` to its right. -/
def MarkerClaim (l w : List Sym) : PassRes → Prop
  | PassRes.stop e L R n =>
      iter n (some ⟨St.B, l, 3, w⟩) = some (cfgAt e.st (L.reverse ++ l) R)
  | PassRes.halt n => iter n (some ⟨St.B, l, 3, w⟩) = none
  | PassRes.other => True

/-- **Every marker event is classified.**  Whatever stands to the right of a
marker, the machine does exactly what `markerF` says: the marker is turned into
a `4`, a pass runs out over the cells to its right, and the pass ends in one of
the four ways of `PassEnd` (or the machine halts). -/
theorem markerF_correct (l w : List Sym) : MarkerClaim l w (markerF w) := by
  have h1 : iter 1 (some (⟨St.B, l, 3, w⟩ : Cfg)) = some (onFirst St.A ((4 : Sym) :: l) w) := by
    cases w <;> rfl
  have h2 := passF_correct 4 w l
  cases hres : passF 4 w with
  | stop e L R n =>
    rw [hres] at h2
    simp only [markerF, hres, PassRes.extend, List.nil_append]
    show iter (n + 1) _ = _
    rw [Nat.add_comm, iter_add, h1]
    exact h2
  | halt n =>
    rw [hres] at h2
    simp only [markerF, hres, PassRes.extend]
    show iter (n + 1) _ = _
    rw [Nat.add_comm, iter_add, h1]
    exact h2
  | other => simp only [markerF, hres, PassRes.extend]; trivial

/-- The marker event is never in the residual case either. -/
theorem markerF_ne_other (w : List Sym) (hw : ∀ s ∈ w, s = 2 ∨ s = 3 ∨ s = 4) :
    markerF w ≠ PassRes.other := by
  simpa [markerF] using passF_ne_other 4 w (by decide) hw

/-! ## Where the surviving `4`s are

A cascade dies as soon as it meets a `4` (`cascade_P_four_stops`,
`cascade_Q_four_stops`), so the fate of the machine depends on whether the word
the outward pass leaves behind contains one.  `ANALYSIS.md` §6.3 lists this as
the third missing item.  Reading off the definition of `passF`, a cell ends up
holding a `4` in exactly two situations:

* it held a `2`, the pass wrote a `3` over it, and the head **bounced** off that
  `3` at the following `4 2` (rule `four_two_of_three`: the fresh marker is
  turned into a `4`);
* it held a `3` — an older marker — crossed as the second cell of a pattern
  `4 3`, and the head did *not* bounce off it immediately afterwards.

Everything else the pass writes is a `3` (over a consumed `2`) or a pair `2 0`
(over a consumed pair `4 4`), and such words are exactly the ones a cascade
crosses.  `PassFwd` describes them, `noFourOut` decides them, and
`halt_of_fresh_four_free` is the resulting halting criterion. -/

/-- Words that a returning cascade crosses, in **tape order**: a `3` for each
`2` the pass consumed, a pair `2 0` for each pair `4 4`.  (`PassRev` of
`Macro.lean` is the same thing listed in the order the cascade meets the cells,
i.e. reversed.) -/
inductive PassFwd : List Sym → Prop
  | nil : PassFwd []
  | three {u : List Sym} : PassFwd u → PassFwd ((3 : Sym) :: u)
  | two_zero {u : List Sym} : PassFwd u → PassFwd ((2 : Sym) :: (0 : Sym) :: u)

theorem passRev_append_three {v : List Sym} (h : PassRev v) : PassRev (v ++ [(3 : Sym)]) := by
  induction h with
  | nil => exact PassRev.three PassRev.nil
  | three _ ih => exact PassRev.three ih
  | zero_two _ ih => exact PassRev.zero_two ih

theorem passRev_append_zero_two {v : List Sym} (h : PassRev v) :
    PassRev (v ++ [(0 : Sym), (2 : Sym)]) := by
  induction h with
  | nil => exact PassRev.zero_two PassRev.nil
  | three _ ih => exact PassRev.three ih
  | zero_two _ ih => exact PassRev.zero_two ih

/-- A `PassFwd` word, read backwards — the order in which the cascade meets its
cells — is a `PassRev` word, and is therefore crossed. -/
theorem passFwd_reverse {u : List Sym} (h : PassFwd u) : PassRev u.reverse := by
  induction h with
  | nil => exact PassRev.nil
  | three _ ih => simpa using passRev_append_three ih
  | two_zero _ ih => simpa using passRev_append_zero_two ih

/-- **Halting from a four-free pass.**  Suppose the outward pass over `w` runs
off the right end of the used tape (`fresh`), and the word it leaves behind is
`q` — the cell it started from, which is not part of the region — followed by a
crossable word ending in a marker `3`.  Then the cascade born at the right end
crosses the whole of that word, and if the cells beyond `q` are crossable too
(`hcross`, in practice the Cantor condition on the counter digits) the machine
halts. -/
theorem halt_of_fresh_four_free {p q : Sym} {w u l : List Sym} {n : ℕ}
    (hpass : passF p w = PassRes.stop PassEnd.fresh (q :: (u ++ [(3 : Sym)])) [3, 2] n)
    (hu : PassFwd u) (hcross : Cross Mode.P q l) :
    ∃ N, iter N (some (onFirst St.A (p :: l) w)) = none := by
  have hc := passF_correct p w l
  rw [hpass] at hc
  have hrev : (q :: (u ++ [(3 : Sym)])).reverse ++ l = (3 : Sym) :: (u.reverse ++ q :: l) := by
    simp
  rw [PassClaim, hrev] at hc
  -- the cascade is born in mode `Q` on the marker the pass has just written
  have hcl : CrossL Mode.P (u.reverse ++ q :: l) := cross_passRev (passFwd_reverse hu) q l hcross
  obtain ⟨x, xs, hx, hiff⟩ := crossL_append_cons (m := Mode.P) u.reverse q l
  have hQ : Cross Mode.Q 3 (u.reverse ++ q :: l) := by
    rw [hx]; exact Cross.Q3 (hiff.mp hcl)
  obtain ⟨k, hk⟩ := cross_halts hQ [] [(2 : Sym)]
  refine ⟨n + k, ?_⟩
  rw [iter_add, hc]
  simpa [PassEnd.st, Mode.sym] using hk

/-! ### Deciding four-freeness without running the pass

`noFourOut p w` inspects the region word `w` from the left, exactly as the pass
does, and returns `some q` — `q` being the symbol the phase cell ends up holding
— precisely when the pass writes no `4` at all.  Comparing it with `passF` shows
what the obstructions are: the pattern `4 3` (an older marker) is four-free only
when the head bounces off it immediately afterwards, the pattern `4 2` met in
phase `3` (a marker just written) always leaves a `4` behind, and the right-edge
patterns `4` and `4 0` leave the `4` they stand on. -/
def noFourOut : Sym → List Sym → Option Sym
  | p, [] => some p
  | p, [Sym.s0] => some p
  | _, Sym.s1 :: _ => none
  | p, Sym.s3 :: _ => some p
  | p, Sym.s2 :: w => if noFourOut 3 w = some 3 then some p else none
  | _, [Sym.s4] => none
  | _, Sym.s4 :: Sym.s0 :: _ => none
  | p, Sym.s4 :: Sym.s3 :: w => if noFourOut 4 w = some 0 then some p else none
  | p, Sym.s4 :: Sym.s4 :: w => if noFourOut 0 w = some 0 then some p else none
  | Sym.s3, Sym.s4 :: Sym.s2 :: w => if noFourOut 0 w = some 0 then some 4 else none
  | Sym.s4, Sym.s4 :: Sym.s2 :: w => if noFourOut 0 w = some 0 then some 0 else none
  | Sym.s0, Sym.s4 :: Sym.s2 :: _ => none
  | Sym.s2, Sym.s4 :: Sym.s2 :: _ => none
  | _, Sym.s4 :: Sym.s2 :: _ => none
  | _, Sym.s4 :: Sym.s1 :: _ => none
  | _, Sym.s0 :: _ => none
  termination_by _ w => w.length

/-- The property `noFourOut` certifies: when the pass ends by giving birth to a
cascade, the word it leaves behind is the (unchanged or bounced) phase cell `q`
followed by a word the cascade crosses. -/
def FourFree (q : Sym) : PassRes → Prop
  | PassRes.stop PassEnd.mark L _ _ => ∃ u, L = q :: u ∧ PassFwd u
  | PassRes.stop PassEnd.fresh L _ _ => ∃ u, L = q :: u ∧ PassFwd u
  | _ => True

theorem fourFree_extend {q q' : Sym} {x : List Sym} {k : ℕ} {res : PassRes}
    (h : FourFree q' res)
    (hx : ∀ u : List Sym, PassFwd u → ∃ u', x ++ q' :: u = q :: u' ∧ PassFwd u') :
    FourFree q (res.extend x k) := by
  cases res with
  | stop e L R n =>
    cases e with
    | turn => trivial
    | turnZero => trivial
    | mark =>
      obtain ⟨u, hu, hpf⟩ := h
      subst hu
      exact hx u hpf
    | fresh =>
      obtain ⟨u, hu, hpf⟩ := h
      subst hu
      exact hx u hpf
  | halt n => trivial
  | other => trivial

/-- **Soundness of the decision procedure.**  If `noFourOut p w = some q` then
the outward pass over `w` leaves behind a word the returning cascade crosses. -/
theorem noFourOut_sound : ∀ (p : Sym) (w : List Sym) (q : Sym),
    noFourOut p w = some q → FourFree q (passF p w) := by
  intro p w
  induction p, w using passF.induct with
  | case1 p =>
    intro q hq
    simp only [noFourOut, Option.some.injEq] at hq
    subst hq
    simp only [passF]
    exact ⟨[], rfl, PassFwd.nil⟩
  | case2 p =>
    intro q hq
    simp only [noFourOut, Option.some.injEq] at hq
    subst hq
    simp only [passF]
    exact ⟨[], rfl, PassFwd.nil⟩
  | case3 p w => intro q hq; simp [noFourOut] at hq
  | case4 p w =>
    intro q hq
    simp only [noFourOut, Option.some.injEq] at hq
    subst hq
    simp only [passF]
    exact ⟨[], rfl, PassFwd.nil⟩
  | case5 p w ih =>
    intro q hq
    simp only [noFourOut] at hq
    split at hq
    · rename_i hcond
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [passF]
      refine fourFree_extend (ih 3 hcond) ?_
      exact fun u hu => ⟨(3 : Sym) :: u, by simp, PassFwd.three hu⟩
    · simp at hq
  | case6 p => intro q hq; simp [noFourOut] at hq
  | case7 p w => intro q hq; simp [noFourOut] at hq
  | case8 p w ih =>
    intro q hq
    simp only [noFourOut] at hq
    split at hq
    · rename_i hcond
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [passF]
      refine fourFree_extend (ih 0 hcond) ?_
      exact fun u hu => ⟨(2 : Sym) :: (0 : Sym) :: u, by simp, PassFwd.two_zero hu⟩
    · simp at hq
  | case9 p w ih =>
    intro q hq
    simp only [noFourOut] at hq
    split at hq
    · rename_i hcond
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [passF]
      refine fourFree_extend (ih 0 hcond) ?_
      exact fun u hu => ⟨(2 : Sym) :: (0 : Sym) :: u, by simp, PassFwd.two_zero hu⟩
    · simp at hq
  | case10 w ih =>
    intro q hq
    simp only [noFourOut] at hq
    split at hq
    · rename_i hcond
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [passF]
      refine fourFree_extend (ih 0 hcond) ?_
      exact fun u hu => ⟨(2 : Sym) :: (0 : Sym) :: u, by simp, PassFwd.two_zero hu⟩
    · simp at hq
  | case11 w ih =>
    intro q hq
    simp only [noFourOut] at hq
    split at hq
    · rename_i hcond
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [passF]
      refine fourFree_extend (ih 0 hcond) ?_
      exact fun u hu => ⟨(2 : Sym) :: (0 : Sym) :: u, by simp, PassFwd.two_zero hu⟩
    · simp at hq
  | case12 w => intro q hq; simp [noFourOut] at hq
  | case13 w => intro q hq; simp [noFourOut] at hq
  | case14 p w h3 h4 h0 h2 =>
    intro q hq
    exfalso
    cases p
    · exact h0 rfl
    · simp [noFourOut] at hq
    · exact h2 rfl
    · exact h3 rfl
    · exact h4 rfl
  | case15 p w => intro q hq; simp [noFourOut] at hq
  | case16 p w h =>
    intro q hq
    cases w with
    | nil => exact absurd rfl h
    | cons a w => simp [noFourOut] at hq

/-- A `PassFwd` word ending in a marker stays a `PassFwd` word when the marker
is removed. -/
theorem passFwd_last_three : ∀ {v : List Sym}, PassFwd v → ∀ u : List Sym,
    v = u ++ [(3 : Sym)] → PassFwd u := by
  intro v h
  induction h with
  | nil => intro u hu; simp at hu
  | @three v _ ih =>
    intro u hu
    cases u with
    | nil =>
      exact PassFwd.nil
    | cons a u0 =>
      simp only [List.cons_append, List.cons.injEq] at hu
      obtain ⟨ha, hv⟩ := hu
      subst ha
      exact PassFwd.three (ih u0 hv)
  | @two_zero v _ ih =>
    intro u hu
    cases u with
    | nil => simp at hu
    | cons a u0 =>
      cases u0 with
      | nil => simp at hu
      | cons b u1 =>
        simp only [List.cons_append, List.cons.injEq] at hu
        obtain ⟨ha, hb, hv⟩ := hu
        subst ha; subst hb
        exact PassFwd.two_zero (ih u1 hv)

/-- **The halting criterion, decided from the region word.**  If the outward
pass over `w` runs off the right end of the used tape, `noFourOut` certifies
that it wrote no `4`, and the last cell it wrote is a marker `3`, then the
cascade born at the right end reaches the cells beyond the region; if those are
crossable, the machine halts. -/
theorem halt_of_noFour_fresh {p q : Sym} {w u l : List Sym} {n : ℕ}
    (hpass : passF p w = PassRes.stop PassEnd.fresh (q :: u) [3, 2] n)
    (hfree : noFourOut p w = some q)
    (hlast : ∃ u' : List Sym, u = u' ++ [(3 : Sym)])
    (hcross : Cross Mode.P q l) :
    ∃ N, iter N (some (onFirst St.A (p :: l) w)) = none := by
  obtain ⟨u', rfl⟩ := hlast
  have hff := noFourOut_sound p w q hfree
  rw [hpass] at hff
  obtain ⟨u0, hu0, hpf⟩ := hff
  have hu0' : u0 = u' ++ [(3 : Sym)] := by simpa using hu0.symm
  subst hu0'
  exact halt_of_fresh_four_free hpass (passFwd_last_three hpf u' rfl) hcross

/-! ### The other side: a `4` in the output kills the cascade

The four-free criterion above says when a cascade *survives* the word the pass
left behind.  The complementary statement is the one a non-halting proof needs:
as soon as the pass has left a `4` — which by the analysis above happens exactly
where the head bounced off a marker — the cascade that the pass gives birth to
travels over the crossable cells, runs into that `4` and is extinguished, and
the machine is alive at every step in between. -/

theorem cascade_step_three (L r : List Sym) :
    iter 1 (some (⟨St.A, L, 3, (2 : Sym) :: r⟩ : Cfg)) =
      some (cfgAt St.A L ((2 : Sym) :: (2 : Sym) :: r)) := by
  cases L <;> rfl

theorem cascade_step_zero_two (L r : List Sym) :
    iter 6 (some (⟨St.A, (2 : Sym) :: L, 0, (2 : Sym) :: r⟩ : Cfg)) =
      some (cfgAt St.A L ((2 : Sym) :: (2 : Sym) :: (4 : Sym) :: r)) := by
  cases L <;> rfl

/-- **A cascade crosses a `PassRev` word.**  In mode `P`, standing on the first
cell of a word left behind by a four-free pass, the cascade traverses the whole
word and arrives, still in mode `P`, on the cell `x` beyond it. -/
theorem passRev_traverse : ∀ {V : List Sym}, PassRev V → ∀ (x : Sym) (l r : List Sym),
    ∃ (N : ℕ) (r' : List Sym),
      iter N (some (cfgAt St.A (V ++ x :: l) ((2 : Sym) :: r))) =
        some ⟨St.A, l, x, (2 : Sym) :: r'⟩ := by
  intro V h
  induction h with
  | nil => intro x l r; exact ⟨0, r, rfl⟩
  | @three u _ ih =>
    intro x l r
    obtain ⟨N, r', hN⟩ := ih x l ((2 : Sym) :: r)
    refine ⟨1 + N, r', ?_⟩
    rw [iter_add]
    have h1 : cfgAt St.A (((3 : Sym) :: u) ++ x :: l) ((2 : Sym) :: r) =
        ⟨St.A, u ++ x :: l, 3, (2 : Sym) :: r⟩ := rfl
    rw [h1, cascade_step_three]
    exact hN
  | @zero_two u _ ih =>
    intro x l r
    obtain ⟨N, r', hN⟩ := ih x l ((2 : Sym) :: (4 : Sym) :: r)
    refine ⟨6 + N, r', ?_⟩
    rw [iter_add]
    have h1 : cfgAt St.A (((0 : Sym) :: (2 : Sym) :: u) ++ x :: l) ((2 : Sym) :: r) =
        ⟨St.A, (2 : Sym) :: (u ++ x :: l), 0, (2 : Sym) :: r⟩ := rfl
    rw [h1, cascade_step_zero_two]
    exact hN

/-- **The cascade dies at the `4`.**  Crossing a four-free pass output and then
meeting a `4`, the cascade is extinguished: the head turns into a left-moving
`B`, and the machine has not halted at any point of the traversal. -/
theorem passRev_dies_at_four {V : List Sym} (hV : PassRev V) (c : Sym) (l r : List Sym) :
    ∃ N, (∀ k ≤ N, iter k (some (cfgAt St.A (V ++ (4 : Sym) :: c :: l) ((2 : Sym) :: r)))
            ≠ none) ∧
      ∃ r', iter N (some (cfgAt St.A (V ++ (4 : Sym) :: c :: l) ((2 : Sym) :: r))) =
        some ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r'⟩ := by
  obtain ⟨N, r', hN⟩ := passRev_traverse hV 4 (c :: l) r
  have hstop : iter (N + 3) (some (cfgAt St.A (V ++ (4 : Sym) :: c :: l) ((2 : Sym) :: r))) =
      some ⟨St.B, l, c, (4 : Sym) :: (4 : Sym) :: r'⟩ := by
    rw [iter_add, hN]
    exact cascade_P_four_stops c l r'
  exact ⟨N + 3, fun k hk => iter_isSome_of_le hstop hk, r', hstop⟩

/-- **A bounce saves the machine.**  Suppose an outward pass ends by running
onto a `3` (so a mode-`P` cascade is born on the last cell it wrote), and the
word it leaves behind consists of crossable cells followed — nearer the counter
— by a `4`.  Then that cascade dies at the `4` and the machine is still running:
the frontier is safe for this excursion.

By the analysis of `noFourOut`, such a `4` is exactly a marker the head bounced
off during the pass. -/
theorem mark_cascade_dies {p c : Sym} {w l v L V z : List Sym} {n : ℕ}
    (hpass : passF p w = PassRes.stop PassEnd.mark L ((2 : Sym) :: v) n)
    (hsplit : L.reverse ++ l = V ++ (4 : Sym) :: c :: z) (hV : PassRev V) :
    ∃ N, (∀ k ≤ N, iter k (some (onFirst St.A (p :: l) w)) ≠ none) ∧
      ∃ r', iter N (some (onFirst St.A (p :: l) w)) =
        some ⟨St.B, z, c, (4 : Sym) :: (4 : Sym) :: r'⟩ := by
  have hc := passF_correct p w l
  rw [hpass, PassClaim, hsplit] at hc
  obtain ⟨N, _, r', hN⟩ := passRev_dies_at_four hV c z v
  have htot : iter (n + N) (some (onFirst St.A (p :: l) w)) =
      some ⟨St.B, z, c, (4 : Sym) :: (4 : Sym) :: r'⟩ := by
    rw [iter_add, hc]
    simpa [PassEnd.st] using hN
  exact ⟨n + N, fun k hk => iter_isSome_of_le htot hk, r', htot⟩

/-- A worked instance of the shield, showing that it is not vacuous: the head
starts a pass in phase `3` over the region `4 2 4 4 3`.  It bounces off the
phase cell at the first `4 2` (leaving the `4` that will stop the cascade),
crosses the pair `4 4`, runs onto the old marker `3` and turns into a cascade,
which crosses the four cells it has just written and dies at that `4`. -/
theorem bounce_example (c : Sym) (z : List Sym) :
    ∃ N, (∀ k ≤ N, iter k (some (⟨St.A, (3 : Sym) :: c :: z, 4,
            [(2 : Sym), 4, 4, 3]⟩ : Cfg)) ≠ none) ∧
      ∃ r', iter N (some (⟨St.A, (3 : Sym) :: c :: z, 4, [(2 : Sym), 4, 4, 3]⟩ : Cfg)) =
        some ⟨St.B, z, c, (4 : Sym) :: (4 : Sym) :: r'⟩ := by
  have hpass : passF 3 [(4 : Sym), 2, 4, 4, 3] =
      PassRes.stop PassEnd.mark [(4 : Sym), 2, 0, 2, 0] ((2 : Sym) :: []) 9 := by
    show passF Sym.s3 [Sym.s4, Sym.s2, Sym.s4, Sym.s4, Sym.s3] =
      PassRes.stop PassEnd.mark [Sym.s4, Sym.s2, Sym.s0, Sym.s2, Sym.s0] [Sym.s2] 9
    simp [passF, PassRes.extend]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  have h := mark_cascade_dies (p := 3) (l := c :: z) (V := [(0 : Sym), 2, 0, 2]) (c := c)
    (z := z) hpass (by simp) (PassRev.zero_two (PassRev.zero_two PassRev.nil))
  simpa [onFirst] using h

/-! ### Consequences for the machine started on the blank tape

The statements above are about arbitrary configurations; they become statements
about the machine through reachability. -/

/-- If the machine ever starts an outward pass, the configuration in which that
pass ends is reachable too — with the exact step count and the exact tape given
by `passF`. -/
theorem reachable_pass {p : Sym} {w l : List Sym} {e : PassEnd} {L R : List Sym} {n : ℕ}
    (hreach : Reachable (onFirst St.A (p :: l) w))
    (hpass : passF p w = PassRes.stop e L R n) :
    Reachable (cfgAt e.st (L.reverse ++ l) R) := by
  have hc := passF_correct p w l
  rw [hpass] at hc
  exact hreach.iter hc

/-- **The halting criterion for the machine.**  If the machine ever reaches a
configuration from which an outward pass runs off the right end of the used
tape leaving no `4` behind and ending on a marker, and the cells beyond the
region are crossable, then the machine halts. -/
theorem halts_of_reachable_noFour_fresh {p q : Sym} {w u l : List Sym} {n : ℕ}
    (hreach : Reachable (onFirst St.A (p :: l) w))
    (hpass : passF p w = PassRes.stop PassEnd.fresh (q :: u) [3, 2] n)
    (hfree : noFourOut p w = some q)
    (hlast : ∃ u' : List Sym, u = u' ++ [(3 : Sym)])
    (hcross : Cross Mode.P q l) : Halts := by
  obtain ⟨N, hN⟩ := halt_of_noFour_fresh hpass hfree hlast hcross
  exact halts_of_reachable hreach hN

/-! ### The converse, checked exhaustively

`noFourOut` is not only sufficient but also necessary: whenever it says `none`,
the pass really does leave a `4` behind in the region.  That is checked here by
evaluation for every region word of length at most `8` and every phase. -/

/-- The cells the pass leaves behind in the region — the cells a cascade born at
the end of the pass has to cross, in tape order — or `none` if the pass ends
without giving birth to a cascade. -/
def PassRes.cascadeOutput : PassRes → Option (List Sym)
  | PassRes.stop PassEnd.mark L _ _ => some L.tail
  | PassRes.stop PassEnd.fresh L _ _ => some L.tail
  | _ => none

/-- The phases a pass can start in. -/
def passPhases : List Sym := [Sym.s0, Sym.s2, Sym.s3, Sym.s4]

/-- All region words of length at most `n` over the symbols `2`, `3`, `4`. -/
def regionWords : ℕ → List (List Sym)
  | 0 => [[]]
  | n + 1 => regionWords n ++
      (regionWords n).flatMap fun w => [Sym.s2, Sym.s3, Sym.s4].map fun s => s :: w

/-- **The decision procedure is exact, on words of length at most `8`.**  If
`noFourOut` returns `none` and the pass gives birth to a cascade, then the word
the pass leaves behind really does contain a `4`, which stops that cascade. -/
theorem noFourOut_complete_upto_eight :
    ∀ p ∈ passPhases, ∀ w ∈ regionWords 8, noFourOut p w = none →
      ((passF p w).cascadeOutput.all fun L => L.contains 4) = true := by
  native_decide

/-- A worked instance: the frontier `1`, then the two cells `2 2`, then fresh
tape.  The pass writes `3 3`, the tape is extended, and the cascade crosses the
two markers and halts the machine.  (The same example as
`Macro.halt_of_frontier_two_twos`, now obtained from the pass *function*.) -/
theorem halt_of_two_twos_pass (l : List Sym) :
    ∃ N, iter N (some (⟨St.A, (1 : Sym) :: l, 2, [(2 : Sym)]⟩ : Cfg)) = none := by
  have hp : passF 1 [(2 : Sym), (2 : Sym)] =
      PassRes.stop PassEnd.fresh ((1 : Sym) :: ([(3 : Sym)] ++ [(3 : Sym)])) [3, 2] 5 := by
    show passF Sym.s1 [Sym.s2, Sym.s2] =
      PassRes.stop PassEnd.fresh [Sym.s1, Sym.s3, Sym.s3] [Sym.s3, Sym.s2] 5
    simp [passF, PassRes.extend]
    exact ⟨rfl, rfl⟩
  have h := halt_of_fresh_four_free (p := 1) (q := 1) (w := [(2 : Sym), (2 : Sym)])
    (u := [(3 : Sym)]) (l := l) (n := 5) hp
    (PassFwd.three PassFwd.nil) Cross.haltP
  simpa [onFirst] using h

end TM2x5
