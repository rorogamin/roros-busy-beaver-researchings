/-
# Audit: the fourteen machines, in bbchallenge notation

This file restates every non-halting result of the project for a machine
given by its standard bbchallenge string, so that the machine being proved
non-halting can be read off directly.

`fromStd s` decodes a string such as `"1RB2LA0RB1LB---_1LA3RA1RA4LB0RB"`:
the transition of state `q` on symbol `i` is the `3`-character chunk number
`i` of the row of `q` (write symbol, move `L`/`R`, next state `A`/`B`), and
`---` means "halt".  For each machine we check, cell by cell, that the
transition table used in the proof is exactly `fromStd s`, and conclude
`¬ Halts (fromStd s) init`: started on the blank tape in state `A`, the
machine never halts.
-/
import RequestProject.BB25.Prefix.Main
import RequestProject.BB25.Prefix.LA.Final
import RequestProject.BB25.Prefix.RB.Final
import RequestProject.BB25.Prefix.LB0.Final
import RequestProject.BB25.Sibling.Final

namespace BB25.Check

open BB25

/-- One transition, from its three characters. -/
def parseCell (w m q : Char) : Option (Sym × Dir × St) :=
  let sym : Option Sym :=
    if w = '0' then some 0 else if w = '1' then some 1 else if w = '2' then some 2
    else if w = '3' then some 3 else if w = '4' then some 4 else none
  let dir : Option Dir := if m = 'L' then some .L else if m = 'R' then some .R else none
  let st : Option St := if q = 'A' then some .A else if q = 'B' then some .B else none
  match sym, dir, st with
  | some a, some d, some s => some (a, d, s)
  | _, _, _ => none

/-- The machine denoted by a bbchallenge string with two states and five
symbols (`---` and any malformed cell mean "halt"). -/
def fromStd (s : String) : Machine := fun q i =>
  let cs := s.toList
  let base := (match q with | .A => 0 | .B => 16) + 3 * i.val
  parseCell (cs.getD base ' ') (cs.getD (base + 1) ' ') (cs.getD (base + 2) ' ')

/-- Two machines agreeing on every state and symbol are equal. -/
theorem machine_ext {m m' : Machine} (h : ∀ q (i : Sym), m q i = m' q i) : m = m' :=
  funext fun q => funext fun i => h q i

macro "table" : tactic =>
  `(tactic| (apply machine_ext; intro q i; cases q <;> fin_cases i <;> rfl))

theorem not_halts_2LB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2LB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2LB" = M b4_2LB by table]
  exact Prefix.not_halts_2LB

theorem not_halts_2RB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2RB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2RB" = M b4_2RB by table]
  exact Prefix.not_halts_2RB

theorem not_halts_1LB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1LB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1LB" = M b4_1LB by table]
  exact Prefix.not_halts_1LB

theorem not_halts_1RB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1RB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1RB" = M b4_1RB by table]
  exact Prefix.not_halts_1RB

theorem not_halts_0LB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0LB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0LB" = M b4_0LB by table]
  exact Prefix.not_halts_0LB

theorem not_halts_0RB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0RB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0RB" = M b4_0RB by table]
  exact Prefix.not_halts_0RB

theorem not_halts_3RA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB3RA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB3RA" = M b4_3RA by table]
  exact Prefix.not_halts_3RA

theorem not_halts_2LA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2LA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2LA" = M b4_2LA by table]
  exact Prefix.not_halts_2LA

theorem not_halts_2RA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2RA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB2RA" = M b4_2RA by table]
  exact Prefix.not_halts_2RA

theorem not_halts_1LA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1LA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1LA" = M b4_1LA by table]
  exact Prefix.not_halts_1LA

theorem not_halts_1RA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1RA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB1RA" = M b4_1RA by table]
  exact Prefix.not_halts_1RA

theorem not_halts_0LA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0LA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0LA" = M b4_0LA by table]
  exact Prefix.not_halts_0LA

theorem not_halts_0RA : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0RA") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0RA" = M b4_0RA by table]
  exact Prefix.not_halts_0RA

/-- The `4RB/0LB` sibling, which is not a member of the family. -/
theorem not_halts_sibling : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4RB0LB") init := by
  rw [show fromStd "1RB2LA0RB1LB---_1LA3RA1RA4RB0LB" = Sibling.machine by table]
  exact Sibling.not_halts_sibling

/-- The start configuration is the blank tape, head in state `A`. -/
theorem init_blank : init = ⟨[], .A, .R, []⟩ := rfl

end BB25.Check
