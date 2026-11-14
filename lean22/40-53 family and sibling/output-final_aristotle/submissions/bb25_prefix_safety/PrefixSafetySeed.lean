/-
Small auxiliary lemmas for PROOF.md.
This file has NOT been compiled in this session. It is intended to be placed
at RequestProject/BB25/PrefixSafetySeed.lean in the supplied Lean project.
It contains no main nonhalting theorem and no placeholders for one.
-/
import RequestProject.BB25.Blocks
import RequestProject.BB25.Nonhalt

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB25.PrefixSafety

abbrev Param := Option (Prod Sym (Prod Dir St))

/-- The bottom-first stack is ZZZXXX; BCfg stores nearest-first. -/
def seedCfg : BCfg :=
  { lt := [.X, .X, .X, .Z, .Z, .Z, .L], st := .Bt, rt := [.Y, .R1] }

/-- No B4 transition is used in this finite prefix. -/
theorem seed_run (b4 : Param) :
    steps (M b4) 156 init = some seedCfg.den := by
  rfl

/-- Left-end XY spinout; the suffix may contain arbitrary symbols. -/
def xyCfg (t : List Sym) : Cfg :=
  { l := [1, 1], q := .A, d := .L, r := 1 :: 1 :: 2 :: 2 :: t }

theorem xy_spinout_step (b4 : Param) (t : List Sym) :
    steps (M b4) 9 (xyCfg t) = some (xyCfg (2 :: t)) := by
  rfl

theorem xy_spinout_iter (b4 : Param) (t : List Sym) : forall j : Nat,
    steps (M b4) (9 * j) (xyCfg t) =
      some (xyCfg (List.replicate j 2 ++ t)) := by
  intro j
  induction j with
  | zero => simp [steps]
  | succ j ih =>
    have hs := xy_spinout_step b4 (List.replicate j 2 ++ t)
    have hr := steps_trans ih hs
    simpa [Nat.mul_add, Nat.mul_one, List.replicate_succ] using hr

theorem not_halts_xy (b4 : Param) (t : List Sym) :
    Not (Halts (M b4) (xyCfg t)) := by
  intro h
  cases h with
  | intro n hn =>
    exact not_halts_within (xy_spinout_iter b4 t n) n (by omega) hn

end BB25.PrefixSafety
