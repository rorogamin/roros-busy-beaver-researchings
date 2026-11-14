import RequestProject.Macro

/-!
# The macro machine

Using the sweep theorems of `RequestProject.Macro` the whole behaviour of
`1LB3RB0LB---2RB_2RA3LA4LB2LB0RA` can be described by a *finite* set of rules on
a much smaller state space:

```
macro configuration  =  (counter digits, cells to the right of the head)
```

The counter digits are the type `LD` of `RequestProject.Macro`, least
significant (nearest the head) first, and the head always sits at the junction
in state `B`.  Every rule below rewrites at most the two cells at the junction
and either pushes one digit onto the counter, increments the counter, or
overflows it.

`mstep_sim` proves that each macro rule is a genuine run of the machine, of at
least one step, for an arbitrary tape context.  Consequently an infinite chain
of macro steps witnesses that the machine never halts; this is carried out in
`RequestProject.OneSafe` (`plus_chain_reaches`).
-/

namespace SOC

open Cfg

/-! ## Local rules in "head cell / next cell" form

These are the rules of `RequestProject.Rules` restated so that they also apply
at the right edge of the written tape, where the cells read are blank. -/

theorem eq_cons_of_hd {r : List Sym} {a : Sym} (h : hd r = a) (ha : a ≠ 0) :
    r = a :: r.tail := by
  match r with
  | [] => exact absurd h.symm ha
  | b :: t => simp [hd] at h; simp [h]

theorem rule44' (l r : List Sym) (h1 : hd r = 4) (h2 : hd r.tail = 4) :
    run ⟨l, St.B, r⟩ 2 = some ⟨2 :: 0 :: l, St.B, r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h1
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule04' (l r : List Sym) (h1 : hd r = 0) (h2 : hd r.tail = 4) :
    run ⟨l, St.B, r⟩ 2 = some ⟨2 :: 2 :: l, St.B, r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h2
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule40' (l r : List Sym) (h1 : hd r = 4) (h2 : hd r.tail = 0) :
    run ⟨l, St.B, r⟩ 4 = some ⟨3 :: 2 :: l, St.B, r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h1
  | a :: t =>
    match t with
    | [] => simp [hd] at h1; subst h1; rfl
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule41' (l r : List Sym) (h1 : hd r = 4) (h2 : hd r.tail = 1) :
    run ⟨l, St.B, r⟩ 2 = some ⟨3 :: 0 :: l, St.B, r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h1
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule01' (l r : List Sym) (h1 : hd r = 0) (h2 : hd r.tail = 1) :
    run ⟨l, St.B, r⟩ 2 = some ⟨3 :: 2 :: l, St.B, r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h2
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule42' (l r : List Sym) (h1 : hd r = 4) (h2 : hd r.tail = 2) :
    run ⟨l, St.B, r⟩ 4 = some ⟨l, St.B, 2 :: 1 :: r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h1
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule00' (l r : List Sym) (h1 : hd r = 0) (h2 : hd r.tail = 0) :
    run ⟨l, St.B, r⟩ 2 = some ⟨l, St.B, 2 :: 1 :: r.tail.tail⟩ := by
  match r with
  | [] => rfl
  | a :: t =>
    match t with
    | [] => simp [hd] at h1; subst h1; rfl
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem rule02' (l r : List Sym) (h1 : hd r = 0) (h2 : hd r.tail = 2) :
    run ⟨l, St.B, r⟩ 2 = some ⟨l, St.B, 2 :: 0 :: r.tail.tail⟩ := by
  match r with
  | [] => simp [hd] at h2
  | a :: t =>
    match t with
    | [] => simp [hd] at h2
    | b :: t' => simp [hd] at h1 h2; subst h1; subst h2; rfl

theorem one1' (l r : List Sym) (h1 : hd r = 1) :
    run ⟨2 :: 2 :: l, St.B, r⟩ 2 = some ⟨l, St.B, 2 :: 0 :: 3 :: r.tail⟩ := by
  rw [eq_cons_of_hd h1 (by decide)]; rfl

theorem one0' (l r : List Sym) (h1 : hd r = 1) :
    run ⟨2 :: 0 :: l, St.B, r⟩ 4 = some ⟨l, St.B, 2 :: 1 :: 3 :: r.tail⟩ := by
  rw [eq_cons_of_hd h1 (by decide)]; rfl

/-! ## The macro machine -/

/-- A macro configuration: the counter `w` (least significant digit first) and
the cells `r` from the head rightwards.  The head is at the junction, in state
`B`, and the tape carries the marker `22` immediately left of the counter. -/
structure MCfg where
  w : List LD
  r : List Sym
deriving DecidableEq, Repr

/-- The tape configuration described by a macro configuration. -/
def enc (m : MCfg) : Cfg := ⟨lzz m.w, St.B, m.r⟩

@[simp] theorem enc_mk (w : List LD) (r : List Sym) :
    enc ⟨w, r⟩ = ⟨lzz w, St.B, r⟩ := rfl

/--
One step of the macro machine.  The rules are, writing `w` for the counter and
using the two cells at the junction (blank cells beyond the written tape):

* `B> 2 r  ⟶  inc(w) B> 4 r` and `B> 3 r ⟶ inc(w) B> 2 r` — a sweep, i.e. `+1`;
* the same two with an overflowing counter — the marker moves one cell left and
  the old counter is released to the right;
* `B> 44 ⟶ 02 B>`, `B> 04 ⟶ 22 B>`, `B> 40 ⟶ 23 B>`, `B> 41 ⟶ 03 B>`,
  `B> 01 ⟶ 23 B>` — a new digit is pushed onto the counter;
* `B> 42 ⟶ B> 21`, `B> 00 ⟶ B> 21`, `B> 02 ⟶ B> 20` — two cells are rewritten
  in place, which sends the head into a sweep;
* `22 B> 1 ⟶ B> 203` and `02 B> 1 ⟶ B> 213` — the terminating `1` of the right
  counter eats the lowest digit of the left counter.

There is deliberately **no** rule for `B> x3` (`x = 0, 4`) nor for reading a `1`
next to a digit `23`/`03`: those are exactly the halting configurations.
-/
inductive MStep : MCfg → MCfg → Prop
  | inc2 {w w' r} : Inc w w' → hd r = 2 → MStep ⟨w, r⟩ ⟨w', 4 :: r.tail⟩
  | inc3 {w w' r} : Inc w w' → hd r = 3 → MStep ⟨w, r⟩ ⟨w', 2 :: r.tail⟩
  | ovf2 {w s r} : Ovf w s → hd r = 2 → MStep ⟨w, r⟩ ⟨[], 4 :: 4 :: (s ++ r.tail)⟩
  | ovf3 {w s r} : Ovf3 w s → hd r = 3 → MStep ⟨w, r⟩ ⟨[], 4 :: (s ++ r.tail)⟩
  | a44 {w r} : hd r = 4 → hd r.tail = 4 → MStep ⟨w, r⟩ ⟨.d0 :: w, r.tail.tail⟩
  | a04 {w r} : hd r = 0 → hd r.tail = 4 → MStep ⟨w, r⟩ ⟨.d1 :: w, r.tail.tail⟩
  | a40 {w r} : hd r = 4 → hd r.tail = 0 → MStep ⟨w, r⟩ ⟨.dA :: w, r.tail.tail⟩
  | a01 {w r} : hd r = 0 → hd r.tail = 1 → MStep ⟨w, r⟩ ⟨.dA :: w, r.tail.tail⟩
  | a41 {w r} : hd r = 4 → hd r.tail = 1 → MStep ⟨w, r⟩ ⟨.dB :: w, r.tail.tail⟩
  | a42 {w r} : hd r = 4 → hd r.tail = 2 → MStep ⟨w, r⟩ ⟨w, 2 :: 1 :: r.tail.tail⟩
  | a00 {w r} : hd r = 0 → hd r.tail = 0 → MStep ⟨w, r⟩ ⟨w, 2 :: 1 :: r.tail.tail⟩
  | a02 {w r} : hd r = 0 → hd r.tail = 2 → MStep ⟨w, r⟩ ⟨w, 2 :: 0 :: r.tail.tail⟩
  | one1 {w r} : hd r = 1 → MStep ⟨.d1 :: w, r⟩ ⟨w, 2 :: 0 :: 3 :: r.tail⟩
  | one0 {w r} : hd r = 1 → MStep ⟨.d0 :: w, r⟩ ⟨w, 2 :: 1 :: 3 :: r.tail⟩

/-- **The macro machine simulates the Turing machine**: every macro step is a
run of at least one step of `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`. -/
theorem mstep_sim {m m' : MCfg} (h : MStep m m') : enc m ⟶+ enc m' := by
  cases h with
  | @inc2 w w' r hinc hr =>
      rw [enc_mk, enc_mk, eq_cons_of_hd hr (by decide)]
      exact inc_sweep hinc r.tail
  | @inc3 w w' r hinc hr =>
      rw [enc_mk, enc_mk, eq_cons_of_hd hr (by decide)]
      exact inc_sweep3 hinc r.tail
  | @ovf2 w s r hovf hr =>
      rw [enc_mk, enc_mk, eq_cons_of_hd hr (by decide)]
      exact ovf_sweep hovf r.tail
  | @ovf3 w s r hovf hr =>
      rw [enc_mk, enc_mk, eq_cons_of_hd hr (by decide)]
      exact ovf_sweep3 hovf r.tail
  | @a44 w r h1 h2 => exact reaches1_of_run (by decide) (rule44' (lzz w) r h1 h2)
  | @a04 w r h1 h2 => exact reaches1_of_run (by decide) (rule04' (lzz w) r h1 h2)
  | @a40 w r h1 h2 => exact reaches1_of_run (by decide) (rule40' (lzz w) r h1 h2)
  | @a01 w r h1 h2 => exact reaches1_of_run (by decide) (rule01' (lzz w) r h1 h2)
  | @a41 w r h1 h2 => exact reaches1_of_run (by decide) (rule41' (lzz w) r h1 h2)
  | @a42 w r h1 h2 => exact reaches1_of_run (by decide) (rule42' (lzz w) r h1 h2)
  | @a00 w r h1 h2 => exact reaches1_of_run (by decide) (rule00' (lzz w) r h1 h2)
  | @a02 w r h1 h2 => exact reaches1_of_run (by decide) (rule02' (lzz w) r h1 h2)
  | @one1 w r h1 => exact reaches1_of_run (by decide) (one1' (lzz w) r h1)
  | @one0 w r h1 => exact reaches1_of_run (by decide) (one0' (lzz w) r h1)

/-! ## Non-halting transfer -/

end SOC
