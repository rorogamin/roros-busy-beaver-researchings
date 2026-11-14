import RequestProject.RunCert

/-!
Finite certificates for NONHALTING_PROOF.md.

STATUS: this file has NOT been compiled in the present environment, which has
no Lean installation. It is a proposed finite-certificate module for the
supplied Lean 4.28.0 project. It does NOT formalize the infinite induction or
claim to prove BB25.Halts false. There are no placeholders or added axioms.

Place this file at RequestProject/TwoEpochCertificate.lean and run:
  lake env lean RequestProject/TwoEpochCertificate.lean

The new semantic lemmas connecting `epoch` with the actual machine, and the
infinite two-epoch price invariant, are specified in FORMALIZATION.md and
proved mathematically in NONHALTING_PROOF.md.
-/

namespace BB25
namespace Macro
namespace TwoEpoch

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- The extra bit at a block, invisible to the old `pat`. -/
def decoration : List Tok -> List Ck
  | [] => []
  | .F :: w => decoration w ++ [.M]
  | .C :: w => decoration w ++ [.M]
  | .P :: w => decoration w ++ [if cap w % 2 = 1 then .S else .B]

/-- The chunk inherited after rebuilding and draining the counter. -/
def emitLabel (c : Ck) (R : Nat) : Ck :=
  match c with
  | .M => .M
  | .S => .M
  | .B => if R % 2 = 1 then .S else .B

def conversion (c : Ck) (R : Nat) : Nat :=
  match c with
  | .B => if R % 2 = 1 then 1 else 0
  | _ => 0

structure Emission where
  word : List Ck
  value : Nat
  conversions : Nat
  deriving DecidableEq, Repr

/-- The capacity scan, its output decoration, and its conversion count. -/
def emitRun : Nat -> List Ck -> Option Emission
  | R, [] => some { word := [], value := R, conversions := 0 }
  | R, c :: cs => do
      let R' <- ckStep c R
      let q <- emitRun R' cs
      pure { word := emitLabel c R :: q.word,
             value := q.value,
             conversions := conversion c R + q.conversions }

/-- The exact proposed overflow map. IMPORTANT: `q.value` is `ckFold`,
not `ckRun`; the low-bit argument to `bitChunks` omits the leading 1. -/
def epoch (cs : List Ck) : Option (List Ck) := do
  let q <- emitRun 0 cs
  if 3 <= q.value then
    let N := q.value + 5
    let t := Nat.size N - 1
    pure (q.word ++ bitChunks (N - 2 ^ t) t)
  else
    none

/-- Iteration fails if any intermediate rebuild/pass domain check fails. -/
def iterate : Nat -> List Ck -> Option (List Ck)
  | 0, cs => some cs
  | n + 1, cs => do
      let ds <- epoch cs
      iterate n ds

def seed5 : List Ck := ck ovfWord5

def base12 : List Ck := (iterate 7 seed5).getD []
def base13 : List Ck := (iterate 8 seed5).getD []

/-- Every paying height and the terminal height is at least m. -/
def deepCheck (m : Nat) : Int -> List Ck -> Bool
  | h, [] => decide ((m : Int) <= h)
  | h, c :: cs =>
      ((!c.pays) || decide ((m : Int) <= h + c.wt)) &&
        deepCheck m (h + c.wt) cs

def payCount (cs : List Ck) : Nat := (cs.filter (fun c => c.pays)).length

def height (cs : List Ck) : Int := (cs.map Ck.wt).sum

def kCount (cs : List Ck) : Nat :=
  ((emitRun 0 cs).map (fun q => q.conversions)).getD 0

def terminalS12 (cs : List Ck) : Prop :=
  cs.drop (cs.length - 12) = List.replicate 12 Ck.S

instance (cs : List Ck) : Decidable (terminalS12 cs) :=
  inferInstanceAs (Decidable (cs.drop (cs.length - 12) = List.replicate 12 Ck.S))

/-- Finite raw entry, with exactly the supplied finite-list tape convention. -/
theorem blank_to_seed :
    steps 4011 init = some (ecfg { dir := .L, w := ovfWord5, s := [3, 2] }) := by
  native_decide

theorem seed_is_overflow : cap ovfWord5 = 0 := by native_decide

theorem seed_decoration : decoration ovfWord5 = seed5 := by native_decide

theorem base12_exists : iterate 7 seed5 = some base12 := by native_decide
theorem base13_exists : iterate 8 seed5 = some base13 := by native_decide
theorem bases_successive : epoch base12 = some base13 := by native_decide

theorem base12_length : base12.length = 479 := by native_decide
theorem base13_length : base13.length = 853 := by native_decide

theorem base12_height : height base12 = 375 := by native_decide
theorem base13_height : height base13 = 621 := by native_decide

theorem base12_deep : deepCheck 50 0 base12 = true := by native_decide
theorem base13_deep : deepCheck 171 0 base13 = true := by native_decide

theorem base12_paying : payCount base12 = 239 := by native_decide
theorem base13_paying : payCount base13 = 426 := by native_decide

theorem base12_terminal : terminalS12 base12 := by native_decide
theorem base13_terminal : terminalS12 base13 := by native_decide

theorem base12_conversions : kCount base12 = 27 := by native_decide
theorem base13_conversions : kCount base13 = 72 := by native_decide

/-- Together with `deepCheck` and `payCount`, these integer inequalities
certify Phi <= 1/8192 without evaluating a large rational expression. -/
theorem base12_integer_bound : (240 : Nat) * 8192 < 2 ^ 50 := by native_decide
theorem base13_integer_bound : (427 : Nat) * 8192 < 2 ^ 171 := by native_decide

end TwoEpoch
end Macro
end BB25
