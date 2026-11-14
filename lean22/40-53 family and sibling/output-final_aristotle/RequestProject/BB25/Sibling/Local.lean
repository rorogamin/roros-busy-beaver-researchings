/-
# The sibling `1RB2LA0RB1LB---_1LA3RA1RA4RB0LB`: the machine and its local rules

The sibling is *not* a member of the family `M b4` (its `B3` is `4RB`).  This
file defines it and checks, by running it, the few rules that are specific to
it or are needed at base level: the new marker rules `03 <B1 → 043 A>` and
`043 <A → <A 101`, the two spinouts, and the `156`-step run from the blank tape
to the `0RB` seed checkpoint.  All other rules are transferred from the block
simulator (`Transfer.lean`).
-/
import RequestProject.BB25.Prefix.RB.Final

namespace BB25.Sibling

/-- The sibling, NOT the original family member with B4 = 0LB. -/
def machine : Machine
  | .A => famA
  | .B => fun s => match s with
    | 0 => some (1, .L, .A)
    | 1 => some (3, .R, .A)
    | 2 => some (1, .R, .A)
    | 3 => some (4, .R, .B)
    | 4 => some (0, .L, .B)

variable (l r : List Sym)

/-- 03 <B1 -> 043 A>, in two base transitions. -/
theorem rule_W_B1 :
    steps machine 2 (Cfg.mk (3 :: 0 :: l) .B .L (1 :: r)) =
      some (Cfg.mk (3 :: 4 :: 0 :: l) .A .R r) := rfl

/-- 043 <A -> <A 101, in three base transitions. -/
theorem rule_Q_A :
    steps machine 3 (Cfg.mk (3 :: 4 :: 0 :: l) .A .L r) =
      some (Cfg.mk l .A .L (1 :: 0 :: 1 :: r)) := rfl

/-! The two spinouts. -/

theorem leftend_B1_run (t : List Sym) :
    steps machine 7 (Cfg.mk [1, 1] .B .L (1 :: t)) =
      some (Cfg.mk [] .A .L (1 :: 1 :: 2 :: 2 :: t)) := rfl

theorem spinout_step (t : List Sym) :
    steps machine 8 (Cfg.mk [] .A .L (1 :: 1 :: 2 :: 2 :: t)) =
      some (Cfg.mk [] .A .L (1 :: 1 :: 2 :: 2 :: 2 :: 2 :: t)) := rfl

theorem xy_spinout_step (t : List Sym) :
    steps machine 9 (Cfg.mk [1, 1] .A .L (1 :: 1 :: 2 :: 2 :: t)) =
      some (Cfg.mk [1, 1] .A .L (1 :: 1 :: 2 :: 2 :: 2 :: t)) := rfl

set_option maxRecDepth 100000 in
/-- The original CP0 seed is reached at exactly the same time. -/
theorem seed_run :
    steps machine 156 init = some (Prefix.cpCfg Prefix.seedStack).den := rfl

end BB25.Sibling
