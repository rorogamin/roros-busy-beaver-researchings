/-
# One epoch dominates the previous one, frontier count included

Two consecutive epochs of `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` scan the *same*
positions of the word: the token at index `j` of the later epoch reads the digit
the token at index `j` of the earlier one wrote, and it sits behind the digit
that the token at index `j-1` wrote.  Comparing the two epochs token by token is
the **lockstep** of this file, and what it carries along is the *frontier
count*: the number of visits that run off the right end of the word.

> **`lockstepT`.**  If an epoch's scan succeeds with frontier count `w ≥ 25`,
> then the next epoch's scan succeeds with a frontier count `w' ≥ 25` as well.

The comparison is carried out with the invariant

* the later epoch reaches each token with at least as many visits, and
* either its token head is no more expensive than the old one, or it is ahead by
  at least one visit,

and the first half of this file is exactly the arithmetic that keeps the
invariant alive, one case per pair of token heads:

* where the old token was cheap, the new one is cheap too and its head is the
  best one, `2` (`chT_le_chT`);
* where both are expensive, the heads stay in the same order and the transfer is
  monotone (`expT_le_expT`);
* where the old token was expensive and the new one is cheap, the new one gains
  a whole visit (`expT_lt_chT`) — which is what pays for the only head that can
  get worse, a loose `1`.

At the end of the word the new epoch walks into the fresh part the old epoch
grew; there the comparison is handed over to `fresh_exit`
(`RequestProject/Exit.lean`), which is what turns the qualitative statement
"the next epoch survives" into the quantitative one "it again sends `25` visits
past the end of its word".  With that, `25 ≤ w` reproduces itself, and the
safety of every epoch — hence the non-halting of the machine — follows by
induction (`RequestProject/NoHalt.lean`).
-/
import RequestProject.Steps
import RequestProject.Exit

namespace ShiftOverflow
namespace Counter

/-! ## The comparison of two tokens

Throughout: `a, t` are the head and the arrival count of the old token, `a', t'`
those of the new one, and the standing hypothesis is

```
a ≤ 2, a' ≤ 2, t ≤ t', (hcost a' ≤ hcost a ∨ t + 1 ≤ t')
```
-/

/-- Cheap against cheap. -/
theorem chT_le_chT {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (htt' : t ≤ t')
    (hd : hcost a' ≤ hcost a ∨ t + 1 ≤ t') : chT a t ≤ chT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [hcost_zero, hcost_one, hcost_two, chT_head_zero, chT_head_one,
        chT_head_two] at hd ⊢ <;> omega

/-- Expensive against expensive. -/
theorem expT_le_expT {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (ht : 2 ≤ t) (htt' : t ≤ t')
    (hd : hcost a' ≤ hcost a ∨ t + 1 ≤ t') : expT a t ≤ expT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [hcost_zero, hcost_one, hcost_two, expT_head_zero, expT_head_one,
        expT_head_two] at hd ⊢ <;> omega

/-- Where the old token was expensive and the new one is cheap, the new one is
ahead by a whole visit — the gain that pays for a loose `1` further on. -/
theorem expT_lt_chT {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (ht : 2 ≤ t) (htt' : t ≤ t') :
    expT a t + 1 ≤ chT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [expT_head_zero, expT_head_one, expT_head_two, chT_head_zero,
        chT_head_one, chT_head_two] <;> omega

/-- A positive frontier count needs at least two visits. -/
theorem frT_pos {a t : ℕ} (ha : a ≤ 2) (h : 1 ≤ frT a t) : 2 ≤ t := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp only [frT_head_zero, frT_head_one, frT_head_two] at h <;> omega

/-- The frontier against an expensive token: if the frontier token left a `3`,
the visits that ran off the end of the old word are no more than the visits the
new token passes on. -/
theorem frT_le_expT {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (ht : 2 ≤ t) (htt' : t ≤ t')
    (hd : hcost a' ≤ hcost a ∨ t + 1 ≤ t') (h3 : frD a t = 3) : frT a t ≤ expT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [hcost_zero, hcost_one, hcost_two, frT_head_zero, frT_head_one,
        frT_head_two, frD_head_zero, frD_head_one, frD_head_two, stDigit_eq_three,
        expT_head_zero, expT_head_one, expT_head_two] at hd h3 ⊢ <;> omega

/-- The frontier against a cheap token whose head is a loose `1`: there the new
token needs three times the old frontier count, and it has it. -/
theorem frT_le_chT_one {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (ht : 2 ≤ t) (htt' : t ≤ t')
    (hd : hcost a' ≤ hcost a ∨ t + 1 ≤ t') (h1 : frD a t = 1) : 3 * frT a t ≤ chT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [hcost_zero, hcost_one, hcost_two, frT_head_zero, frT_head_one,
        frT_head_two, frD_head_zero, frD_head_one, frD_head_two, stDigit_eq_one,
        chT_head_zero, chT_head_one, chT_head_two] at hd h1 ⊢ <;> omega

/-- The frontier against a cheap token whose head is a `0`. -/
theorem frT_le_chT_zero {a a' t t' : ℕ} (ha : a ≤ 2) (ha' : a' ≤ 2) (ht : 2 ≤ t) (htt' : t ≤ t') :
    frT a t ≤ chT a' t' := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    rcases (by omega : a' = 0 ∨ a' = 1 ∨ a' = 2) with rfl | rfl | rfl <;>
      simp only [frT_head_zero, frT_head_one, frT_head_two, chT_head_zero,
        chT_head_one, chT_head_two] <;> omega

/-! ## The lockstep -/

/-- **One epoch dominates the previous one, frontier count included.**  Let the
old epoch scan `a :: rest` with `t` visits, successfully, leaving the word `o`
and sending `w ≥ 25` visits past the end of the word.  Let the new epoch scan
`a' :: o` with `t' ≥ t` visits and a head that is either no more expensive than
`a` or compensated by one extra visit.  Then the new epoch's scan succeeds too,
and it also sends at least `25` visits past the end of its word. -/
theorem lockstepT : ∀ (n : ℕ) (a : ℕ) (rest : List ℕ), rest.length = n →
    ∀ (t : ℕ) (o : List ℕ) (w a' t' : ℕ),
      scan t (a :: rest) = some o → scanT t (a :: rest) = some w → 25 ≤ w →
      a' ≤ 2 → t ≤ t' → (hcost a' ≤ hcost a ∨ t + 1 ≤ t') →
      ∃ w', scanT t' (a' :: o) = some w' ∧ 25 ≤ w' := by
  intro n
  induction n with
  | zero =>
      intro a rest hrest t o w a' t' hscan hscanT hw ha' htt' hd
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero hrest
      subst hnil
      have hsome : (scan t [a]).isSome := by rw [hscan]; simp
      have ha : a ≤ 2 := scan_head_le hsome
      have ht : 1 ≤ t := scan_pos hsome
      rw [scan_last ha ht] at hscan
      rw [scanT_last ha ht] at hscanT
      have hwv : frT a t = w := by simpa using hscanT
      have ho : o = frD a t :: freshW (frT a t) := by simpa using hscan.symm
      subst ho
      have hw' : 1 ≤ frT a t := by omega
      have ht2 : 2 ≤ t := frT_pos ha hw'
      by_cases h3 : frD a t = 3
      · rw [h3, scanT_exp ha' (by omega)]
        have hle : frT a t ≤ expT a' t' := frT_le_expT ha ha' ht2 htt' hd h3
        exact fresh_exit (v := frT a t) (b := 0) (u := expT a' t') (by omega) (by omega)
          (by simpa using hle)
      · have hne2 : frD a t ≠ 2 := by unfold frD; split_ifs <;> exact stDigit_ne_two _
        have hle3 := frD_le_three a t
        rw [scanT_cheap ha' (by omega) h3]
        by_cases h1 : frD a t = 1
        · have hone : 3 * frT a t ≤ chT a' t' := frT_le_chT_one ha ha' ht2 htt' hd h1
          rw [h1]
          exact fresh_exit (v := frT a t) (b := 1) (u := chT a' t') (by omega) (by omega)
            (by simp only [pen_one]; omega)
        · have hzero : frT a t ≤ chT a' t' := frT_le_chT_zero ha ha' ht2 htt'
          have h0 : frD a t = 0 := by omega
          rw [h0]
          exact fresh_exit (v := frT a t) (b := 0) (u := chT a' t') (by omega) (by omega)
            (by simpa using hzero)
  | succ k ih =>
      intro a rest hrest t o w a' t' hscan hscanT hw ha' htt' hd
      match rest, hrest with
      | c :: rest', hrest =>
        have hlen : rest'.length = k := by simpa using hrest
        have hsome : (scan t (a :: c :: rest')).isSome := by rw [hscan]; simp
        have ha : a ≤ 2 := scan_head_le hsome
        have ht : 1 ≤ t := scan_pos hsome
        by_cases hc : c = 3
        · subst hc
          have ht2 : 2 ≤ t := scan_exp_pos hsome
          rw [scan_exp ha ht2] at hscan
          rw [scanT_exp ha ht2] at hscanT
          obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.1 hscan
          have hmono : expT a t ≤ expT a' t' := expT_le_expT ha ha' ht2 htt' hd
          have hgain : expT a t + 1 ≤ chT a' t' := expT_lt_chT ha ha' ht2 htt'
          have hne2 : expD a t ≠ 2 := by unfold expD; split_ifs <;> exact stDigit_ne_two _
          by_cases h3 : expD a t = 3
          · rw [h3, scanT_exp ha' (by omega)]
            exact ih 0 rest' hlen (expT a t) o2 w 0 (expT a' t') ho2 hscanT hw
              (by omega) hmono (Or.inl (by simp))
          · rw [scanT_cheap ha' (by omega) h3]
            have hle3 := expD_le_three a t
            by_cases h1 : expD a t = 1
            · rw [h1]
              exact ih 0 rest' hlen (expT a t) o2 w 1 (chT a' t') ho2 hscanT hw
                (by omega) (by omega) (Or.inr (by omega))
            · have h0 : expD a t = 0 := by omega
              rw [h0]
              exact ih 0 rest' hlen (expT a t) o2 w 0 (chT a' t') ho2 hscanT hw
                (by omega) (by omega) (Or.inl (by simp))
        · rw [scan_cheap ha ht hc] at hscan
          rw [scanT_cheap ha ht hc] at hscanT
          obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.1 hscan
          rw [scanT_cheap ha' (by omega) (by norm_num)]
          have hmono : chT a t ≤ chT a' t' := chT_le_chT ha ha' htt' hd
          exact ih c rest' hlen (chT a t) o2 w 2 (chT a' t') ho2 hscanT hw
            (by omega) hmono (Or.inl (by simp))

end Counter
end ShiftOverflow
