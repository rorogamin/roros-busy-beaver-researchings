/-
  CET(4) — two 4-state, 2-symbol machines on one shared tape.

  STATUS: this file is the *statement* layer. It fixes the semantics and states
  the conjectures. It proves nothing about halting or non-halting for any
  machine. Read proof/README.md before using it.

  Rules, taken from the pipeline in the parent directory:

    * A step: both agents read the current tape in their own state, then both
      write, then both move. Reads are simultaneous and use the old tape.
    * If both heads sit on the same cell and write, agent 1's write wins.
    * The pair HALTS when, *after* a step, the two heads occupy the same cell.
      Collision at time 0 is excluded: the heads start at 0 and 2.
    * Both tapes start blank (all `false`). Both agents start in state A.
-/
namespace CET4

-- The conjecture lemmas split on undecidable propositions.
open Classical

inductive Dir
  | L
  | R
deriving DecidableEq, Repr

/-- One cell of a transition table: what to write, where to move, next state. -/
structure Move where
  write : Bool
  dir : Dir
  next : Fin 4
deriving DecidableEq, Repr

/-- A 4-state, 2-symbol transition table, indexed by (state, symbol read). -/
abbrev Table := Fin 4 → Bool → Move

/-- A CET(4) machine: two agents sharing one tape. -/
structure Pair where
  name : String
  a1 : Table
  a2 : Table

/-- A full configuration: the tape and both heads. The tape is a total
    function `Int → Bool`, so it is unbounded in both directions; untouched
    cells are `false` (symbol 0). -/
structure Config where
  tape : Int → Bool
  p1 : Int
  p2 : Int
  s1 : Fin 4
  s2 : Fin 4

/-- Blank tape, heads at 0 and 2, both agents in state A. -/
def init (M : Pair) : Config :=
  { tape := fun _ => false, p1 := 0, p2 := 2, s1 := (0 : Fin 4), s2 := (0 : Fin 4) }

/-- The tape after one step: agent 1's write wins a shared cell. -/
def nextTape (M : Pair) (c : Config) : Int → Bool :=
  fun i =>
    if i = c.p2 then (M.a2 c.s2 (c.tape c.p2)).write
    else if i = c.p1 then (M.a1 c.s1 (c.tape c.p1)).write
    else c.tape i

/-- One lockstep step. -/
def step (M : Pair) (c : Config) : Config :=
  let t := nextTape M c
  let m1 := M.a1 c.s1 (c.tape c.p1)
  let m2 := M.a2 c.s2 (c.tape c.p2)
  { tape := t
    p1 := c.p1 + (if m1.dir = Dir.R then (1 : Int) else (-1 : Int))
    p2 := c.p2 + (if m2.dir = Dir.R then (1 : Int) else (-1 : Int))
    s1 := m1.next
    s2 := m2.next }

/-- The configuration after `t` steps from the blank-tape start. -/
def run (M : Pair) : Nat → Config
  | 0 => init M
  | n + 1 => step M (run M n)

/-- The pair halts: after some positive number of steps the heads collide. -/
def Halts (M : Pair) : Prop :=
  ∃ t : Nat, 1 ≤ t ∧ (run M t).p1 = (run M t).p2

/-- The pair halts within `N` steps. This is decidable in principle and is the
    only kind of halting claim a computer can ever establish. -/
def HaltsBy (M : Pair) (N : Nat) : Prop :=
  ∃ t : Nat, 1 ≤ t ∧ t ≤ N ∧ (run M t).p1 = (run M t).p2

/-- The pair never halts: the heads never collide after any step. -/
def NonHalts (M : Pair) : Prop :=
  ∀ t : Nat, 1 ≤ t → (run M t).p1 ≠ (run M t).p2

def AllHalt (L : List Pair) : Prop := ∀ M, M ∈ L → Halts M

def NoneHalt (L : List Pair) : Prop := ∀ M, M ∈ L → NonHalts M

/-- CONJECTURE C: the ladder is mixed — at least one machine halts and at least
    one does not. Incompatible with both `AllHalt` and `NoneHalt`. -/
def Mixed (L : List Pair) : Prop :=
  (∃ M, M ∈ L ∧ Halts M) ∧ (∃ M, M ∈ L ∧ NonHalts M)

/-! ### What is genuinely provable here

  The lemmas below are about the *logic* of the three conjectures, not about any
  machine. `trichotomy` and the exclusions make the three-way framing rigorous;
  none of them says anything about which case the ladder is in. -/

/-- Every pair either halts or never halts. This is just the decidability of a
    propositional quantifier; it carries no information about which. -/
theorem halts_or_nonhalts (M : Pair) : Halts M ∨ NonHalts M := by
  by_cases h : Halts M
  · exact Or.inl h
  · right
    intro t ht heq
    exact h ⟨t, ht, heq⟩

/-- A halting pair is not a non-halting pair. -/
theorem halts_not_nonHalts (M : Pair) : Halts M → ¬ NonHalts M := by
  rintro ⟨t, ht, heq⟩ hn
  exact hn t ht heq

/-- `Mixed` rules out `AllHalt`. -/
theorem mixed_not_allHalt (L : List Pair) (h : Mixed L) : ¬ AllHalt L := by
  rintro hA
  rcases h with ⟨_, ⟨M, hM, hn⟩⟩
  exact (halts_not_nonHalts M (hA M hM)) hn

/-- `Mixed` rules out `NoneHalt`. -/
theorem mixed_not_noneHalt (L : List Pair) (h : Mixed L) : ¬ NoneHalt L := by
  rintro hB
  rcases h with ⟨⟨M, hM, hh⟩, _⟩
  exact (halts_not_nonHalts M hh) (hB M hM)

/-- The three conjectures exhaust the possibilities. This is a tautology of
    classical logic, not a claim about any machine: it says every ladder is
    all-halting, all-non-halting, or mixed, and says nothing about which.
    With `allHalt_and_noneHalt_contradict` and the two lemmas above, exactly one
    of the three holds for any non-empty ladder. -/
theorem trichotomy (L : List Pair) : AllHalt L ∨ NoneHalt L ∨ Mixed L := by
  by_cases hA : AllHalt L
  · exact Or.inl hA
  · by_cases hB : NoneHalt L
    · exact Or.inr (Or.inl hB)
    · right; right
      constructor
      · apply Classical.byContradiction
        intro h
        apply hB
        intro M hM
        by_cases hh : Halts M
        · exact (h ⟨M, hM, hh⟩).elim
        · exact (halts_or_nonhalts M).resolve_left hh
      · apply Classical.byContradiction
        intro h
        apply hA
        intro M hM
        by_cases hh : Halts M
        · exact hh
        · exact (h ⟨M, hM, (halts_or_nonhalts M).resolve_left hh⟩).elim

/-- `AllHalt` and `NoneHalt` cannot both hold for a non-empty ladder. This is
    the reason the two proofs requested for this project cannot both exist:
    at least one of them must be a proof of a false statement. -/
theorem allHalt_and_noneHalt_contradict (L : List Pair) (hne : L ≠ []) :
    ¬ (AllHalt L ∧ NoneHalt L) := by
  rintro ⟨ha, hn⟩
  cases L with
  | nil => exact hne rfl
  | cons M Ms =>
      exact halts_not_nonHalts M (ha M (List.mem_cons_self M Ms))

        (hn M (List.mem_cons_self M Ms))

end CET4
