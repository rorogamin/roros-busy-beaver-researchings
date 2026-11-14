/-
# The frontier count of the next epoch stays large

`RequestProject/Terminal.lean` shows that the fresh part of a word is *safe* for
the next epoch: it gets through.  This file proves the quantitative form of the
same statement, which is what makes the whole argument go round:

> **`fresh_exit`.**  If the fresh part was grown by `v ≥ 25` visits and the next
> epoch arrives at it with at least as many visits (three times as many behind a
> loose `1`), then it *leaves* the fresh part with at least `25` visits again.

Since those leaving visits are exactly the frontier count of the next epoch,
`25 ≤ w` reproduces itself from one epoch to the next, and the safety of every
epoch follows by induction.

## How it is proved

Along the fresh part write `v` for the visits that grew the current cell and `u`
for the visits arriving at it.  A cell is **expensive** when `3 ∣ v`; there `u`
and `v` are both multiplied by about `2/3`, so the *ratio* `u/v` is unchanged.
At a **cheap** cell `u` doubles while `v` still falls to `2v/3`: the ratio gains
a factor of three.  The exit count is about two thirds of the last `u`, so

```
exit ≈ 2 · 3 ^ (number of cheap cells).
```

Three cheap cells are therefore enough, and the proof is a chain of four
invariants, each an explicit inequality between `u` and `v` that is preserved by
an expensive cell and improved by a cheap one:

| phase | invariant | side condition |
| --- | --- | --- |
| 0 | `v ≤ u` | `400 ≤ postRun (v+3)` |
| 1 | `5(v+3) ≤ 2(u+3)` | `30 ≤ postRun (v+3)` |
| 2 | `7(v+3) ≤ u+3` | `4 ≤ postRun (v+3)` |
| 3 | `14(v+3) ≤ u+3` | — |

The side conditions are what forbids an endless run of expensive cells: by
`RequestProject/PostRun.lean` an expensive step leaves `postRun (v+3)` alone
while `v` falls, so a run must end, and `n ^ 17 ≤ postRun n ^ 27` says that when
it ends the count is still large enough to reach the next phase.

Phase 0 needs `postRun (v + 3) ≥ 400`, which holds as soon as `v ≥ 14000`
(`le_postRun`).  Below that the statement is checked by evaluation
(`fresh_exit_small`), for the tight arrival `u = v` only — which is enough,
because a larger arrival count can only help (`scanT_mono`).
-/
import RequestProject.Steps
import RequestProject.PostRun

namespace ShiftOverflow
namespace Counter

/-! ## The fresh part, cell by cell

The three unfolding rules of a traversal of `b :: freshW V`, one for each
residue of `V` mod three. -/

theorem fresh_exp {V : ℕ} (hV : 0 < V) (h : V % 3 = 0) {b u : ℕ} (hb : b ≤ 2) (hu : 2 ≤ u) :
    scanT u (b :: freshW V) = scanT (expT b u) (0 :: freshW (V - 1 - V / 3)) := by
  rw [freshW_mod_zero hV h, scanT_exp hb hu]

theorem fresh_cheap_one {V : ℕ} (h : V % 3 = 1) {b u : ℕ} (hb : b ≤ 2) (hu : 1 ≤ u) :
    scanT u (b :: freshW V) = scanT (chT b u) (1 :: freshW (V - 1 - V / 3)) := by
  rw [freshW_mod_one h, scanT_cheap hb hu (by norm_num)]

theorem fresh_cheap_zero {V : ℕ} (h : V % 3 = 2) {b u : ℕ} (hb : b ≤ 2) (hu : 1 ≤ u) :
    scanT u (b :: freshW V) = scanT (chT b u) (0 :: freshW (V - 1 - V / 3)) := by
  rw [freshW_mod_two h, scanT_cheap hb hu (by norm_num)]

/-! ## More visits never hurt

Every transfer of the scan is monotone in the number of arriving visits, so a
traversal that succeeds with `u` visits succeeds with more, and leaves at least
as many. -/

theorem scanT_mono : ∀ (n : ℕ) (s : List ℕ), s.length = n → ∀ (u u' w : ℕ), u ≤ u' →
    scanT u s = some w → ∃ w', scanT u' s = some w' ∧ w ≤ w' := by
  intro n
  induction n with
  | zero =>
      intro s hs u u' w huu' h
      match s with
      | [] =>
          refine ⟨u', by simp [scanT], ?_⟩
          have : w = u := by simpa [scanT] using h.symm
          omega
      | _ :: _ => simp at hs
  | succ k ih =>
      intro s hs u u' w huu' h
      match s with
      | [] => simp at hs
      | [a] =>
          have hu : 1 ≤ u := by
            rcases Nat.eq_zero_or_pos u with rfl | hu
            · rw [scanT_zero_cons] at h; simp at h
            · exact hu
          have ha : a ≤ 2 := by
            by_contra hcon
            simp only [scanT] at h
            split_ifs at h <;> simp_all
          rw [scanT_last ha hu] at h
          refine ⟨frT a u', scanT_last ha (by omega), ?_⟩
          have hw : w = frT a u := by simpa using h.symm
          subst hw
          rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
            simp only [frT_head_zero, frT_head_one, frT_head_two] <;> omega
      | a :: c :: rest =>
          have hlen : rest.length = k - 1 + 1 ∨ rest.length + 2 = k + 1 := by
            simp at hs; omega
          have hu : 1 ≤ u := by
            rcases Nat.eq_zero_or_pos u with rfl | hu
            · rw [scanT_zero_cons] at h; simp at h
            · exact hu
          have ha : a ≤ 2 := by
            by_contra hcon
            simp only [scanT] at h
            split_ifs at h <;> simp_all
          by_cases hc : c = 3
          · subst hc
            have hu2 : 2 ≤ u := by
              by_contra hcon
              have hu1 : u = 1 := by omega
              subst hu1
              rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
                simp [scanT, cycE_zero_eq, scanT_zero_cons] at h
            rw [scanT_exp ha hu2] at h
            rw [scanT_exp ha (by omega)]
            have hmono : expT a u ≤ expT a u' := by
              rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
                simp only [expT_head_zero, expT_head_one, expT_head_two] <;> omega
            exact ih (0 :: rest) (by simp at hs ⊢; omega) _ _ w hmono h
          · rw [scanT_cheap ha hu hc] at h
            rw [scanT_cheap ha (by omega) hc]
            have hmono : chT a u ≤ chT a u' := by
              rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
                simp only [chT_head_zero, chT_head_one, chT_head_two] <;> omega
            exact ih (c :: rest) (by simp at hs ⊢; omega) _ _ w hmono h

/-- More arriving visits leave at least as many visits at the frontier. -/
theorem fresh_mono {v b u u' w : ℕ} (huu' : u ≤ u')
    (h : scanT u (b :: freshW v) = some w) :
    ∃ w', scanT u' (b :: freshW v) = some w' ∧ w ≤ w' :=
  scanT_mono _ _ rfl u u' w huu' h

/-! ## The penalty of a loose `1`

A traversal that arrives behind a loose `1` needs a little more than one that
arrives behind a `0` or a `2`; `pen` is where that surcharge is written. -/

/-- `1` behind a loose `1`, `0` behind any other head. -/
def pen (b : ℕ) : ℕ := if b = 1 then 1 else 0

@[simp] theorem pen_zero : pen 0 = 0 := rfl
@[simp] theorem pen_one : pen 1 = 1 := rfl
@[simp] theorem pen_two : pen 2 = 0 := rfl

/-! ## Phase 3: a rich arrival gets through with `25` visits to spare -/

/-- **The rich phase.**  If the arriving count is fourteen times the growing
count, the traversal leaves the fresh part with at least `25` visits. -/
theorem rich_exit : ∀ (v b u : ℕ), b ≤ 2 → 14 * (v + 3) + 3 * pen b ≤ u + 3 →
    ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ V ih =>
    intro b u hb hinv
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp only [pen_zero, pen_one, pen_two] at hinv
    all_goals {
      rcases Nat.eq_zero_or_pos V with rfl | hV
      · rw [freshW_zero, scanT_last hb (by omega)]
        refine ⟨frT _ u, rfl, ?_⟩
        simp only [frT_head_zero, frT_head_one, frT_head_two]
        omega
      · have hlt : V - 1 - V / 3 < V := by omega
        rcases (by omega : V % 3 = 0 ∨ V % 3 = 1 ∨ V % 3 = 2) with h | h | h
        · rw [fresh_exp hV h hb (by omega)]
          refine ih _ hlt 0 _ (by omega) ?_
          simp only [expT_head_zero, expT_head_one, expT_head_two, pen_zero]
          omega
        · rw [fresh_cheap_one h hb (by omega)]
          refine ih _ hlt 1 _ (by omega) ?_
          simp only [chT_head_zero, chT_head_one, chT_head_two, pen_one]
          omega
        · rw [fresh_cheap_zero h hb (by omega)]
          refine ih _ hlt 0 _ (by omega) ?_
          simp only [chT_head_zero, chT_head_one, chT_head_two, pen_zero]
          omega
    }

/-! ## Phases 2, 1, 0: how a tight arrival becomes a rich one

Each phase is the same induction as the rich one, with two differences: its
invariant is weaker, and it carries a side condition on `postRun (v + 3)`.  An
expensive cell leaves both the invariant and the side condition intact while
`v` falls, so the induction can run; a cheap cell multiplies the invariant's
constant by about three and hands the traversal to the next phase, the side
condition of which follows from `n ^ 17 ≤ postRun n ^ 27`. -/

/-- An expensive cell does not move the end of the run. -/
theorem postRun_step {V : ℕ} (hV : 0 < V) (h : V % 3 = 0) :
    postRun (V + 3) = postRun (V - 1 - V / 3 + 3) := by
  have hdvd : (3 : ℕ) ∣ V + 3 := by omega
  have hhalf : 2 * (V + 3) / 3 = V - 1 - V / 3 + 3 := by omega
  rw [postRun_of_dvd (by omega) hdvd, hhalf]

/-- **Phase 2.**  A sevenfold arrival, one cheap cell short of the rich phase. -/
theorem phase2_exit : ∀ (v b u : ℕ), b ≤ 2 → 4 ≤ postRun (v + 3) →
    7 * (v + 3) + 3 * pen b ≤ u + 3 → ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ V ih =>
    intro b u hb hside hinv
    have hV : 0 < V := by
      have := postRun_le (V + 3); omega
    have hlt : V - 1 - V / 3 < V := by omega
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp only [pen_zero, pen_one, pen_two] at hinv
    all_goals {
      rcases (by omega : V % 3 = 0 ∨ V % 3 = 1 ∨ V % 3 = 2) with h | h | h
      · rw [fresh_exp hV h hb (by omega)]
        refine ih _ hlt 0 _ (by omega) (by rw [← postRun_step hV h]; exact hside) ?_
        simp only [expT_head_zero, expT_head_one, expT_head_two, pen_zero]
        omega
      · rw [fresh_cheap_one h hb (by omega)]
        refine rich_exit _ 1 _ (by omega) ?_
        simp only [chT_head_zero, chT_head_one, chT_head_two, pen_one]
        omega
      · rw [fresh_cheap_zero h hb (by omega)]
        refine rich_exit _ 0 _ (by omega) ?_
        simp only [chT_head_zero, chT_head_one, chT_head_two, pen_zero]
        omega
    }

/-- **Phase 1.**  Two and a half times the growing count, two cheap cells short
of the rich phase. -/
theorem phase1_exit : ∀ (v b u : ℕ), b ≤ 2 → 30 ≤ postRun (v + 3) →
    5 * (v + 3) + 6 * pen b ≤ 2 * (u + 3) → ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ V ih =>
    intro b u hb hside hinv
    have hV : 27 ≤ V := by
      have := postRun_le (V + 3); omega
    have hlt : V - 1 - V / 3 < V := by omega
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp only [pen_zero, pen_one, pen_two] at hinv
    all_goals {
      rcases (by omega : V % 3 = 0 ∨ V % 3 = 1 ∨ V % 3 = 2) with h | h | h
      · rw [fresh_exp (by omega) h hb (by omega)]
        refine ih _ hlt 0 _ (by omega) (by rw [← postRun_step (by omega) h]; exact hside) ?_
        simp only [expT_head_zero, expT_head_one, expT_head_two, pen_zero]
        omega
      all_goals {
        -- a cheap cell: the end of the run is the cell itself, so `V + 3 ≥ 30`
        have hfree : ¬ (3 : ℕ) ∣ V + 3 := by omega
        have hn : 30 ≤ V + 3 := by rw [postRun_of_not_dvd hfree] at hside; exact hside
        have hside' : 4 ≤ postRun (V - 1 - V / 3 + 3) := by
          refine le_postRun (n := V - 1 - V / 3 + 3) ?_
          calc (4 : ℕ) ^ 27 ≤ 20 ^ 17 := by norm_num
            _ ≤ (V - 1 - V / 3 + 3) ^ 17 := Nat.pow_le_pow_left (by omega) 17
        first
        | (rw [fresh_cheap_one h hb (by omega)]
           refine phase2_exit _ 1 _ (by omega) hside' ?_
           simp only [chT_head_zero, chT_head_one, chT_head_two, pen_one]
           omega)
        | (rw [fresh_cheap_zero h hb (by omega)]
           refine phase2_exit _ 0 _ (by omega) hside' ?_
           simp only [chT_head_zero, chT_head_one, chT_head_two, pen_zero]
           omega)
      }
    }

/-- **Phase 0.**  The arrival the lockstep delivers: as many visits as grew the
cells, three times as many behind a loose `1`. -/
theorem phase0_exit : ∀ (v b u : ℕ), b ≤ 2 → 400 ≤ postRun (v + 3) →
    v + 2 * v * pen b ≤ u → ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ V ih =>
    intro b u hb hside hinv
    have hV : 397 ≤ V := by
      have := postRun_le (V + 3); omega
    have hlt : V - 1 - V / 3 < V := by omega
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp only [pen_zero, pen_one, pen_two] at hinv
    all_goals {
      rcases (by omega : V % 3 = 0 ∨ V % 3 = 1 ∨ V % 3 = 2) with h | h | h
      · rw [fresh_exp (by omega) h hb (by omega)]
        refine ih _ hlt 0 _ (by omega) (by rw [← postRun_step (by omega) h]; exact hside) ?_
        simp only [expT_head_zero, expT_head_one, expT_head_two, pen_zero]
        omega
      all_goals {
        have hfree : ¬ (3 : ℕ) ∣ V + 3 := by omega
        have hn : 400 ≤ V + 3 := by rw [postRun_of_not_dvd hfree] at hside; exact hside
        have hside' : 30 ≤ postRun (V - 1 - V / 3 + 3) := by
          refine le_postRun (n := V - 1 - V / 3 + 3) ?_
          calc (30 : ℕ) ^ 27 ≤ 266 ^ 17 := by norm_num
            _ ≤ (V - 1 - V / 3 + 3) ^ 17 := Nat.pow_le_pow_left (by omega) 17
        first
        | (rw [fresh_cheap_one h hb (by omega)]
           refine phase1_exit _ 1 _ (by omega) hside' ?_
           simp only [chT_head_zero, chT_head_one, chT_head_two, pen_one]
           omega)
        | (rw [fresh_cheap_zero h hb (by omega)]
           refine phase1_exit _ 0 _ (by omega) hside' ?_
           simp only [chT_head_zero, chT_head_one, chT_head_two, pen_zero]
           omega)
      }
    }

/-! ## Small fresh parts, by evaluation

Phase 0 needs `postRun (v + 3) ≥ 400`, which `le_postRun` gives as soon as
`v ≥ 14000`.  For the fresh parts below that the statement is checked by
running the traversal, and only for the tight arrival `u = v` (`u = 3v` behind
a loose `1`), which is enough by `fresh_mono`. -/

/-- The traversal of `freshW v` from `u` visits behind the head `b`, as a
decision procedure: does it get through and leave `25` visits? -/
def exitOKb (v b u : ℕ) : Bool :=
  match scanT u (b :: freshW v) with
  | some w => decide (25 ≤ w)
  | none => false

theorem exit_of_exitOKb {v b u : ℕ} (h : exitOKb v b u = true) :
    ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  have key : ∀ (o : Option ℕ),
      (match o with | some w => decide (25 ≤ w) | none => false) = true →
      ∃ w, o = some w ∧ 25 ≤ w := by
    rintro (_ | w) hh
    · simp at hh
    · exact ⟨w, rfl, by simpa using hh⟩
  exact key _ h

/-- Every fresh part grown by between `25` and `14000` visits is left with at
least `25` visits by the tight arrival. -/
theorem exit_small_check :
    (List.range 14000).all (fun v => decide (v < 25) ||
      (exitOKb v 0 v && exitOKb v 2 v && exitOKb v 1 (3 * v))) = true := by
  native_decide

theorem exit_small {v b u : ℕ} (hb : b ≤ 2) (h25 : 25 ≤ v) (hlt : v < 14000)
    (hinv : v + 2 * v * pen b ≤ u) : ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  have hall := List.all_eq_true.1 exit_small_check v (List.mem_range.2 hlt)
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true] at hall
  rcases hall with hcon | ⟨⟨h0, h2⟩, h1⟩
  · omega
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp only [pen_zero, pen_one, pen_two] at hinv
    · obtain ⟨w, hw, hw25⟩ := exit_of_exitOKb h0
      obtain ⟨w', hw', hle⟩ := fresh_mono (u' := u) (by omega) hw
      exact ⟨w', hw', by omega⟩
    · obtain ⟨w, hw, hw25⟩ := exit_of_exitOKb h1
      obtain ⟨w', hw', hle⟩ := fresh_mono (u' := u) (by omega) hw
      exact ⟨w', hw', by omega⟩
    · obtain ⟨w, hw, hw25⟩ := exit_of_exitOKb h2
      obtain ⟨w', hw', hle⟩ := fresh_mono (u' := u) (by omega) hw
      exact ⟨w', hw', by omega⟩

/-! ## The frontier count reproduces itself -/

/-- **The fresh part hands on a large frontier count.**  A fresh part grown by
`v ≥ 25` visits, entered with at least as many visits as grew it (three times as
many behind a loose `1`), is left with at least `25` visits again.

Those leaving visits are the frontier count of the next epoch, so this is the
statement that reproduces itself from epoch to epoch. -/
theorem fresh_exit {v b u : ℕ} (hb : b ≤ 2) (h25 : 25 ≤ v) (hinv : v + 2 * v * pen b ≤ u) :
    ∃ w, scanT u (b :: freshW v) = some w ∧ 25 ≤ w := by
  rcases Nat.lt_or_ge v 14000 with hlt | hge
  · exact exit_small hb h25 hlt hinv
  · refine phase0_exit v b u hb ?_ hinv
    refine le_postRun (n := v + 3) ?_
    calc (400 : ℕ) ^ 27 ≤ 14003 ^ 17 := by norm_num
      _ ≤ (v + 3) ^ 17 := Nat.pow_le_pow_left (by omega) 17

end Counter
end ShiftOverflow
