import RequestProject.Machine

/-!
# Local ("macro") rules for `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`

All the rules below are statements about *arbitrary* contexts `l` (the tape to the
left of the head, nearest cell first) and `r` (the tape to the right of the head):
they describe what the machine does to a bounded window of the tape, whatever the
rest of the tape looks like.

Throughout, a configuration `⟨l, B, x :: y :: r⟩` is drawn as `l |B> x y r` and
corresponds to the notation `… B> x y …` of the informal analysis.
-/

namespace SOC

open Cfg

/-! ## The eight "head moves right / stays" rules

These need no information at all about the tape to the left of the head. -/

/-- `B> 44  ⟶  02 B>` (2 steps). -/
theorem rule_44 (l r : List Sym) :
    run ⟨l, St.B, 4 :: 4 :: r⟩ 2 = some ⟨2 :: 0 :: l, St.B, r⟩ := rfl

/-- `B> 41  ⟶  03 B>` (2 steps). -/
theorem rule_41 (l r : List Sym) :
    run ⟨l, St.B, 4 :: 1 :: r⟩ 2 = some ⟨3 :: 0 :: l, St.B, r⟩ := rfl

/-- `B> 40  ⟶  23 B>` (4 steps). -/
theorem rule_40 (l r : List Sym) :
    run ⟨l, St.B, 4 :: 0 :: r⟩ 4 = some ⟨3 :: 2 :: l, St.B, r⟩ := rfl

/-- `B> 42  ⟶  B> 21` (4 steps, the head does not move). -/
theorem rule_42 (l r : List Sym) :
    run ⟨l, St.B, 4 :: 2 :: r⟩ 4 = some ⟨l, St.B, 2 :: 1 :: r⟩ := rfl

/-! ## The leftward sweep

In state `B`, symbols `2` and `3` make the head move left, rewriting `2 ↦ 4` and
`3 ↦ 2`.  This is the "`<`" (decrement) operation of the informal analysis: the
head runs left across the left counter until it meets a `0`. -/

/-! ## Decrementing the left counter

The left counter is written as a sequence of two-cell digits `02`, `22`, `23`,
`03` (leftmost cell first).  A decrement (`<` in the informal analysis) sweeps
left across `2`s and `3`s until it meets the `0` of a digit `02` or `03`:
a digit `02` stops the sweep (and becomes `22`), while a digit `03` lets the
borrow propagate further left. -/

/-! ## Absorbing a run of `4`s

A block of `2n` consecutive `4`s in front of the head is turned into `n` digits
`02` of the left counter. -/

/-! ## Overflow rules

These are the four "right overflow" rules and the "left overflow" rule of the
informal analysis. -/

/-! ## Reading the final `1` of the right counter from a left digit

When the head reads the `1` it moves left *in state `A`*.  The cell it lands on
is the right-hand cell of the adjacent left digit: `2` for the digits `02`, `22`
and `3` for the digits `23`, `03`.  In the latter case the machine halts, which
is why the informal analysis always records the adjacent digit as `(02|22)`. -/

/-! ## The halting configurations

The machine halts exactly when state `A` reads a `3`.  State `A` is entered by
`B0` and `B4` (moving right) and by `B1` (moving left), so the machine halts
iff the head, in state `B`, reads a `0` or a `4` with a `3` on its right, or
reads a `1` with a `3` on its left. -/

end SOC
