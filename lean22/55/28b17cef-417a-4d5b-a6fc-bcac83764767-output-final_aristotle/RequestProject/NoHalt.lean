/-
# `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` never halts

This file puts the pieces together.

* `RequestProject/ModelSpec.lean` — the counter model *is* the machine: if every
  iterate of the one-epoch map `epochF` succeeds, the machine never halts.
* `RequestProject/Exit.lean` — a fresh part grown by `v ≥ 25` visits and entered
  with at least as many visits is left with at least `25` visits.
* `RequestProject/Lockstep.lean` — one epoch dominates the previous one, so a
  frontier count of at least `25` is handed on from each epoch to the next.

So the property

> **`WordRich L`** — the scan of `L` succeeds and at least `25` visits run off
> the right end of the word

reproduces itself (`wordRich_step`), it holds at the machine's fourth epoch
boundary (`seed_rich`, by evaluation), and therefore it holds for ever.  Every
epoch of the machine then succeeds, and the machine never halts:

> **`never_halts`.**  `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` started on the blank
> tape does not halt, at any number of steps.
-/
import RequestProject.Lockstep
import RequestProject.ModelSpec

namespace ShiftOverflow
namespace Counter

/-- **A rich word.**  The scan of `L` succeeds and at least `25` visits reach
the frontier, so the next word gains a long fresh piece at its right end. -/
def WordRich (L : List ℕ) : Prop := ∃ w, scanT 1 (0 :: L) = some w ∧ 25 ≤ w

/-- The decision procedure behind `WordRich`. -/
def richB (L : List ℕ) : Bool :=
  match scanT 1 (0 :: L) with
  | some w => decide (25 ≤ w)
  | none => false

theorem wordRich_of_richB {L : List ℕ} (h : richB L = true) : WordRich L := by
  have key : ∀ (o : Option ℕ),
      (match o with | some w => decide (25 ≤ w) | none => false) = true →
      ∃ w, o = some w ∧ 25 ≤ w := by
    rintro (_ | w) hh
    · simp at hh
    · exact ⟨w, rfl, by simpa using hh⟩
  exact key _ h

/-- A rich word is scanned successfully. -/
theorem epochF_isSome_of_rich {L : List ℕ} (h : WordRich L) : (epochF L).isSome := by
  obtain ⟨w, hw, _⟩ := h
  have : (scanT 1 (0 :: L)).isSome := by rw [hw]; simp
  exact (scanT_isSome_iff (0 :: L).length (0 :: L) rfl 1).1 this

/-- **Richness reproduces itself.**  If the word `L` is rich and the epoch turns
it into `L'`, then `L'` is rich as well. -/
theorem wordRich_step {L L' : List ℕ} (hL : epochF L = some L') (h : WordRich L) :
    WordRich L' := by
  obtain ⟨w, hw, hw25⟩ := h
  exact lockstepT L.length 0 L rfl 1 L' w 0 1 hL hw hw25 (by norm_num) le_rfl (Or.inl le_rfl)

/-- The machine's fourth epoch boundary is rich: `78` visits run off the end of
its word.  Checked by evaluating the counter model. -/
theorem seed_rich_check :
    (match epochIter 4 [] with | some L => richB L | none => false) = true := by
  native_decide

theorem seed_rich : ∃ L, epochIter 4 [] = some L ∧ WordRich L := by
  have key : ∀ (o : Option (List ℕ)),
      (match o with | some L => richB L | none => false) = true →
      ∃ L, o = some L ∧ WordRich L := by
    rintro (_ | L) hh
    · simp at hh
    · exact ⟨L, rfl, wordRich_of_richB hh⟩
  exact key _ seed_rich_check

/-! ## The model survives for ever -/

/-- The iterates of the model are cut off from the right: if the model survives
`n` epochs it has survived all the earlier ones. -/
theorem epochIter_isSome_of_le {m n : ℕ} (hmn : m ≤ n) (h : (epochIter n []).isSome) :
    (epochIter m []).isSome := by
  induction n with
  | zero => rw [show m = 0 from by omega]; exact h
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · refine ih (by omega) ?_
        rcases hprev : epochIter n [] with _ | L
        · rw [epochIter, hprev] at h; simp at h
        · simp
      · have : m = n + 1 := by omega
        subst this; exact h

/-- Every word the machine reaches from its fourth epoch boundary on is rich. -/
theorem rich_forever : ∀ k, ∃ L, epochIter (4 + k) [] = some L ∧ WordRich L := by
  intro k
  induction k with
  | zero => simpa using seed_rich
  | succ k ih =>
      obtain ⟨L, hL, hrich⟩ := ih
      obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.1 (epochF_isSome_of_rich hrich)
      refine ⟨L', ?_, wordRich_step hL' hrich⟩
      rw [show 4 + (k + 1) = (4 + k) + 1 from rfl, epochIter, hL, Option.bind_some, hL']

/-- **The model survives every epoch.** -/
theorem model_survives : ∀ n, (epochIter n []).isSome := by
  intro n
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · obtain ⟨L, hL, _⟩ := rich_forever 0
    refine epochIter_isSome_of_le (m := n) (n := 4) (by omega) ?_
    rw [show (4 : ℕ) = 4 + 0 from rfl, hL]; simp
  · obtain ⟨L, hL, _⟩ := rich_forever (n - 4)
    rw [show 4 + (n - 4) = n from by omega] at hL
    rw [hL]; simp

/-! ## Non-halting -/

/-- **`1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` never halts.**  Started on the blank
tape, the machine is still running after every number of steps. -/
theorem never_halts : ∀ n, steps n init ≠ none :=
  never_halts_of_model model_survives

end Counter
end ShiftOverflow
