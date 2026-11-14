/-
  Machine 14: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`

  This file formalizes the *block abstraction* supplied for this machine and
  a raw five-symbol zipper interface.  The abstraction has three head modes
  (`<`, `>`, `w>`) and the following blocks:

    left  side: L U W F Y Q
    right side: R X V C C1 C2 P

  The key point of this file is that the partition is built into the types:
  `BState.left` is a `List LTok` and `BState.right` is a `List RTok`.  Thus a
  state cannot mix the two sides.  The invariant `Inv` only has to record the
  two blocks that are never removed, `L` on the left and `R` on the right.

  What is proved:

  * `stepB_inv`: every defined block rule preserves the partition invariant;
  * `partition_insufficient`: the supplied partition invariant does **not**
    imply that the block simulation can continue;
  * `gt_R_stuck`: the missing context is exactly `>` reading `R`, which has no
    rule in the supplied table.

  This is a fresh proof attempt that found a precise obstruction, not a
  nonhalting proof.  `raw_prefix_14` proves the concrete raw prefix reaches
  `initRaw`, and `raw_first_macro` proves the first raw step.  The universal
  raw-to-block bridge is in `Machine14Bridge.lean`: `rawOf_stepB` implements
  every defined block rule by a raw macro of at most six steps, and
  `rawRun_bridges_runB` reaches every defined block stage from `rawStart`.
  What remains for a nonhalting proof is not the local bridge but a block
  invariant that excludes the `> R` dead end and proves the block run total.
-/

set_option maxHeartbeats 4000000

namespace M14

/-- Blocks that live on the left of the active head. -/
inductive LTok
  | L
  | U
  | W
  | F
  | Y
  | Q
  deriving DecidableEq, Repr

/-- Blocks that live on the right of the active head. -/
inductive RTok
  | R
  | X
  | V
  | C
  | C1
  | C2
  | P
  deriving DecidableEq, Repr

/-- The three head modes of the block model. -/
inductive Head
  | l
  | r
  | wr
  deriving DecidableEq, Repr

/-- A block configuration.  `left` is stored nearest-to-head first. -/
structure BState where
  head : Head
  left : List LTok
  right : List RTok
  deriving DecidableEq, Repr

/-- The only structural facts the rules need: `L` is never removed on the left,
and `R` is never removed on the right. -/
structure Inv (s : BState) : Prop where
  hasL : LTok.L ∈ s.left
  hasR : RTok.R ∈ s.right

/-- One block macro step.  The fallback `none` is unreachable on `Inv` states. -/
def stepB (s : BState) : Option BState :=
  match s.head, s.left, s.right with
  | Head.l, LTok.W :: rest, r => some ⟨Head.l, rest, RTok.V :: r⟩
  | Head.l, LTok.U :: rest, r => some ⟨Head.r, LTok.W :: rest, r⟩
  | Head.l, LTok.L :: rest, r => some ⟨Head.wr, LTok.L :: rest, r⟩
  | Head.l, LTok.Y :: rest, r => some ⟨Head.l, rest, RTok.X :: r⟩
  | Head.l, LTok.F :: rest, r => some ⟨Head.l, rest, RTok.C :: r⟩
  | Head.l, LTok.Q :: rest, r => some ⟨Head.l, rest, RTok.P :: r⟩
  | Head.r, l, RTok.V :: rest => some ⟨Head.r, LTok.U :: l, rest⟩
  | Head.r, l, RTok.X :: rest => some ⟨Head.l, l, RTok.C1 :: RTok.P :: rest⟩
  | Head.r, l, RTok.C :: rest => some ⟨Head.l, l, RTok.C1 :: rest⟩
  | Head.r, l, RTok.C1 :: rest => some ⟨Head.l, l, RTok.C2 :: rest⟩
  | Head.r, l, RTok.C2 :: rest => some ⟨Head.r, LTok.F :: l, rest⟩
  | Head.r, l, RTok.P :: rest => some ⟨Head.wr, l, rest⟩
  | Head.wr, l, RTok.V :: rest => some ⟨Head.wr, LTok.U :: l, rest⟩
  | Head.wr, l, RTok.X :: rest => some ⟨Head.wr, LTok.Y :: l, rest⟩
  | Head.wr, l, RTok.R :: rest => some ⟨Head.l, l, RTok.X :: RTok.R :: rest⟩
  | Head.wr, l, RTok.C :: rest => some ⟨Head.r, LTok.Q :: LTok.F :: l, rest⟩
  | Head.wr, l, RTok.C1 :: rest => some ⟨Head.r, LTok.Q :: LTok.U :: l, rest⟩
  | Head.wr, l, RTok.C2 :: rest => some ⟨Head.wr, LTok.W :: l, rest⟩
  | Head.wr, l, RTok.P :: rest => some ⟨Head.r, LTok.U :: l, rest⟩
  | _, _, _ => none

/-- The supplied start of the block simulation, after the 14-step raw prefix. -/
def initB : BState :=
  ⟨Head.l, [LTok.Q, LTok.U, LTok.L], [RTok.R]⟩

theorem initB_inv : Inv initB := by
  constructor <;> simp [initB]

/-- A block step lifted to `Option`. -/
def ostepB (o : Option BState) : Option BState := o.bind stepB

/-- The block run. -/
def runB : Nat → Option BState
  | 0 => some initB
  | n + 1 => ostepB (runB n)

/-- The block abstraction halts. -/
def HaltsB : Prop := ∃ n : Nat, runB n = none

/-- The block model is **not** total on the supplied partition invariant: `>`
reading `R` has no rule.  This is the block-model shadow of the one remaining
halting route: a `>` head reaching the right-end block `21$`. -/
theorem gt_R_stuck : stepB ⟨Head.r, [LTok.L], [RTok.R]⟩ = none := rfl

theorem gt_R_partition : Inv ⟨Head.r, [LTok.L], [RTok.R]⟩ := by
  constructor <;> simp

/-- The supplied partition invariant alone does not imply that the block
simulation can continue. -/
theorem partition_insufficient :
    ∃ s : BState, Inv s ∧ stepB s = none :=
  ⟨_, gt_R_partition, gt_R_stuck⟩

/-- Every defined block step preserves the partition invariant.  The `> R`
case is vacuous (`stepB` is `none`), which is exactly the obstruction above. -/
theorem stepB_inv {s s' : BState} (h : Inv s) (hs : stepB s = some s') : Inv s' := by
  rcases s with ⟨head, left, right⟩
  cases h with
  | mk hL hR =>
      unfold stepB at hs
      split at hs <;>
        first
        | (rw [Option.some.injEq] at hs
           subst s'
           constructor <;> simp_all)
        | (simp at hs)

/-- What would still be needed for a block-level nonhalting proof: an invariant
that excludes `>` reading `R` forever.  The partition alone is insufficient.
`runB` is still defined below so the missing statement can be stated precisely. -/
def AvoidsGtR (s : BState) : Prop :=
  ¬ (s.head = Head.r ∧ ∃ rest : List RTok, s.right = RTok.R :: rest)

/-- The avoidance condition is exactly what the supplied invariant does not
provide; this example satisfies the partition and violates `AvoidsGtR`. -/
theorem gt_R_not_avoids : ¬ AvoidsGtR ⟨Head.r, [LTok.L], [RTok.R]⟩ := by
  intro h
  exact h ⟨rfl, ⟨[], rfl⟩⟩

/-- `AvoidsGtR` is not inductive by itself: `> V R` is allowed and steps to
`> R`.  Thus the block proof needs a stronger relation than merely forbidding
the final stuck context. -/
theorem avoids_not_inductive :
    ∃ s s' : BState, AvoidsGtR s ∧ stepB s = some s' ∧ ¬ AvoidsGtR s' := by
  refine ⟨⟨Head.r, [LTok.L], [RTok.V, RTok.R]⟩,
    ⟨Head.r, [LTok.U, LTok.L], [RTok.R]⟩, ?_, rfl, ?_⟩
  · simp [AvoidsGtR]
  · simp [AvoidsGtR]

/-! ## Raw five-symbol interface and finite safety certificate -/

/-- Raw machine 14 configuration: state `0=A`, `1=B`; `left` is nearest-first. -/
structure RState where
  st : Nat
  left : List Nat
  cur : Nat
  right : List Nat
  deriving DecidableEq, Repr

namespace RState

def wL (c : RState) (w : Nat) (s : Nat) : RState :=
  match c.left with
  | [] => ⟨s, [], 0, w :: c.right⟩
  | x :: xs => ⟨s, xs, x, w :: c.right⟩

def wR (c : RState) (w : Nat) (s : Nat) : RState :=
  match c.right with
  | [] => ⟨s, w :: c.left, 0, []⟩
  | x :: xs => ⟨s, w :: c.left, x, xs⟩

end RState

/-- Raw transitions of `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`. -/
def rawStep (c : RState) : Option RState :=
  match c.st, c.cur with
  | 0, 0 => some (c.wR 1 1)
  | 0, 1 => some (c.wL 2 0)
  | 0, 2 => some (c.wR 0 1)
  | 0, 3 => some (c.wL 4 1)
  | 0, 4 => some (c.wR 1 0)
  | 1, 0 => some (c.wL 1 0)
  | 1, 1 => some (c.wR 3 0)
  | 1, 2 => some (c.wR 1 0)
  | 1, 3 => none
  | 1, 4 => some (c.wL 0 0)
  | _, _ => none

/-- Raw configuration after 14 ordinary steps, `L U Q < R`. -/
def initRaw : RState := ⟨0, [1, 0, 1, 1], 1, [1]⟩

/-- The raw machine starts in state A on an all-blank tape. -/
def rawStart : RState := ⟨0, [], 0, []⟩

/-- Iterated raw execution. -/
def rawRun : Nat → Option RState
  | 0 => some rawStart
  | n + 1 => (rawRun n).bind rawStep

/-- The concrete 14-step raw prefix lands exactly on `initRaw`, the start of
    the block simulation.  This is a finite computation, not the universal
    raw-to-block simulation theorem. -/
theorem raw_prefix_14 : rawRun 14 = some initRaw := by
  decide

/-- The first block rule `Q < -> < P` in raw form. -/
theorem raw_first_macro :
    rawStep initRaw = some ⟨0, [0, 1, 1], 1, [2, 1]⟩ := rfl

/-- A `>` head whose right context is `(V|C2)* R` can reach the stuck `> R`. -/
def badR : List RTok → Bool
  | [] => false
  | RTok.V :: xs => badR xs
  | RTok.C2 :: xs => badR xs
  | RTok.R :: _ => true
  | _ => false

/-- The dual bad language for a `w>` head. -/
def badW : List RTok → Bool
  | [] => false
  | RTok.V :: xs => badW xs
  | RTok.X :: xs => badW xs
  | RTok.C2 :: xs => badW xs
  | RTok.C :: xs => badR xs
  | RTok.C1 :: xs => badR xs
  | RTok.P :: xs => badR xs
  | _ => false

def safeB (s : BState) : Bool :=
  (if s.head = Head.r then !badR s.right else true) &&
  (if s.head = Head.wr then !badW s.right else true)

def checkSafe : Nat → Option BState → Bool
  | 0, _ => true
  | _n + 1, none => false
  | n + 1, some s => safeB s && checkSafe n (stepB s)

/-- Machine-checked finite safety certificate; this is not the universal invariant. -/
theorem safe_checked_million : checkSafe 1000000 (some initB) = true := by
  native_decide

#print axioms M14.raw_prefix_14
#print axioms M14.raw_first_macro
#print axioms M14.safe_checked_million
#print axioms M14.gt_R_stuck
#print axioms M14.partition_insufficient
#print axioms M14.stepB_inv
#print axioms M14.avoids_not_inductive

end M14
