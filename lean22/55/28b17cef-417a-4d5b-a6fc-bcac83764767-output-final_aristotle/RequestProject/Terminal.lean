/-
# The frontier of the counter: where the word grows

`RequestProject/DigitModel.lean` runs one epoch of
`1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` as a single scan of the word.  The scan ends
at the **frontier**: the visits that run off the end of the used tape grow a
fresh piece of word, `freshW t`, out of `t` visits.  That `t` — the number of
visits that reach the frontier — is the one number of an epoch that this file
isolates (`scanT`), because every question about the next epoch turns out to be
a question about it.

What this file provides is that number and the description of the fresh part it
grows.  `scanT` is the scan of `RequestProject/DigitModel.lean` run for the
frontier count alone: it succeeds exactly when the scan itself succeeds
(`scanT_isSome_iff`), and its value is the number of visits that run off the
right end of the word.  The fresh part those visits grow, `freshW v`, is read
off cell by cell (`freshW_mod_zero`, `freshW_mod_one`, `freshW_mod_two`):
writing `v` for the visits that grew a cell, the cell holds

| `v mod 3` | the cell holds | and the rest is grown by |
| --- | --- | --- |
| `0` | `3` — a radix-3/2 cell | `≈ 2v/3 − 1` |
| `1` | `1` — a cheap cell | `≈ 2v/3` |
| `2` | `0` — a cheap cell | `≈ 2v/3` |

which is the recursion `RequestProject/Exit.lean` walks along.
-/
import RequestProject.DigitModel

namespace ShiftOverflow
namespace Counter

/-! ## Arithmetic of the radix-3/2 digit -/

theorem cycE_zero_eq (t : ℕ) : cycE t 0 = t - (t + 2) / 3 := by unfold cycE; norm_num

theorem cycE_one_eq (t : ℕ) : cycE t 1 = t - t / 3 := by unfold cycE; norm_num; omega

theorem cycE_two_eq (t : ℕ) : cycE t 2 = t - (t + 1) / 3 := by
  unfold cycE; norm_num; omega

/-! ## The cost of a token head

A token `(a, c)` with `c ≠ 3` passes on `2t - hcost a` visits: the head `2` is
free, a `0` eats one visit and a loose `1` eats two.  The same order governs the
expensive tokens, and `hcost` is how the two scans of a lockstep comparison are
kept in order. -/

/-- What the head of a token costs it: `2 ↦ 0`, `0 ↦ 1`, `1 ↦ 2`. -/
def hcost (a : ℕ) : ℕ := if a = 2 then 0 else if a = 0 then 1 else 2

@[simp] theorem hcost_two : hcost 2 = 0 := rfl
@[simp] theorem hcost_zero : hcost 0 = 1 := rfl
@[simp] theorem hcost_one : hcost 1 = 2 := rfl


/-! ## The frontier count -/

/-- **The frontier count.**  `scanT t s` is the number of visits that reach the
frontier during the scan `scan t s`: the `w` with which the word grows by
`freshW w`.  It fails exactly where `scan` fails. -/
def scanT : ℕ → List ℕ → Option ℕ
  | t, [] => some t
  | t, [a] =>
      if t = 0 then none
      else if a = 0 then some (cycE (t - 1) 2)
      else if a = 1 then some (cycE (t - 1) 0)
      else if a = 2 then some (cycE t 0)
      else none
  | t, a :: c :: rest =>
      if t = 0 then none
      else if c = 3 then
        if a = 2 then scanT (cycE (t - 1) 0) (0 :: rest)
        else if a = 0 then
          if t < 2 then none else scanT (cycE (t - 1) 1 - 1) (0 :: rest)
        else if a = 1 then
          if t < 2 then none else scanT (cycE (t - 2) 0) (0 :: rest)
        else none
      else
        if a = 2 then scanT (2 * t) (c :: rest)
        else if a = 0 then scanT (2 * t - 1) (c :: rest)
        else if a = 1 then scanT (2 * t - 2) (c :: rest)
        else none

/-- The two runs of the scan fail together: `scanT` succeeds exactly when
`scan` does. -/
theorem scanT_isSome_iff : ∀ (n : ℕ) (s : List ℕ), s.length = n → ∀ (t : ℕ),
    (scanT t s).isSome ↔ (scan t s).isSome := by
  intro n
  induction n with
  | zero =>
      intro s hs t
      match s with
      | [] => simp [scan, scanT]
      | _ :: _ => simp at hs
  | succ k ih =>
      intro s hs t
      match s with
      | [] => simp at hs
      | [a] =>
          simp only [scan, scanT]
          split_ifs <;> simp
      | a :: c :: rest =>
          simp only [List.length_cons] at hs
          have ih1 := ih (c :: rest) (by simp; omega)
          have ih2 := ih (0 :: rest) (by simp; omega)
          simp only [scan, scanT]
          split_ifs <;> simp [ih1, ih2]

/-! ## Unfolding the fresh word -/

theorem freshW_zero : freshW 0 = [] := by rw [freshW]

theorem freshW_succ (v : ℕ) :
    freshW (v + 1) = stDigit (cycS v 2) :: freshW (cycE v 2) := by rw [freshW]

/-- A fresh cell grown by a multiple of three visits holds a `3`: it is a
radix-3/2 cell, the expensive kind. -/
theorem freshW_mod_zero {V : ℕ} (hV : 0 < V) (h : V % 3 = 0) :
    freshW V = 3 :: freshW (V - 1 - V / 3) := by
  obtain ⟨v, rfl⟩ : ∃ v, V = v + 1 := ⟨V - 1, by omega⟩
  rw [freshW_succ]
  have hd : stDigit (cycS v 2) = 3 := by unfold stDigit cycS; split_ifs <;> omega
  have he : cycE v 2 = v + 1 - 1 - (v + 1) / 3 := by rw [cycE_two_eq]; omega
  rw [hd, he]

/-- A fresh cell grown by `1 mod 3` visits holds a `1`. -/
theorem freshW_mod_one {V : ℕ} (h : V % 3 = 1) :
    freshW V = 1 :: freshW (V - 1 - V / 3) := by
  obtain ⟨v, rfl⟩ : ∃ v, V = v + 1 := ⟨V - 1, by omega⟩
  rw [freshW_succ]
  have hd : stDigit (cycS v 2) = 1 := by unfold stDigit cycS; split_ifs <;> omega
  have he : cycE v 2 = v + 1 - 1 - (v + 1) / 3 := by rw [cycE_two_eq]; omega
  rw [hd, he]

/-- A fresh cell grown by `2 mod 3` visits holds a `0`. -/
theorem freshW_mod_two {V : ℕ} (h : V % 3 = 2) :
    freshW V = 0 :: freshW (V - 1 - V / 3) := by
  obtain ⟨v, rfl⟩ : ∃ v, V = v + 1 := ⟨V - 1, by omega⟩
  rw [freshW_succ]
  have hd : stDigit (cycS v 2) = 0 := by unfold stDigit cycS; split_ifs <;> omega
  have he : cycE v 2 = v + 1 - 1 - (v + 1) / 3 := by rw [cycE_two_eq]; omega
  rw [hd, he]

end Counter
end ShiftOverflow
