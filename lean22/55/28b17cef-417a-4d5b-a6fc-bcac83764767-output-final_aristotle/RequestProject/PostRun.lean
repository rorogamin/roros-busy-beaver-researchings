/-
# The end of an expensive run

Along the fresh part of a word the arrival count and the count that grew the
cells shrink in step at every **expensive** (radix-3/2) cell, and only a
**cheap** cell lets the arriving epoch gain.  So the one thing a proof of
survival has to know is that expensive cells cannot go on for ever, and by how
much the count has dropped when they stop.

Write `n = v + 3` for the count `v` that still has to grow, shifted by three.
The growth step `v ↦ v - 1 - v/3` is, in this variable, exactly

```
n ↦ ⌈2n/3⌉,
```

and a cell is expensive precisely when `3 ∣ n`.  While `3 ∣ n` the step is
`n ↦ 2n/3`, which divides the power of three in `n` by exactly three: an
expensive run is as long as the `3`-adic valuation of `n`, and it ends at

```
postRun n = 2 ^ v₃(n) * (n / 3 ^ v₃(n)).
```

The number `postRun n` is what this file is about.  It is unchanged by an
expensive step — that is `postRun_of_dvd` — and it is never much smaller than
`n` itself: `n ^ 17 ≤ (postRun n) ^ 27`, because `3 ^ 17 ≤ 2 ^ 27`.  That single
inequality is what makes a long expensive run expensive for the *word* as well:
the longer the run, the larger `n` had to be to pay for it.
-/
import Mathlib

namespace ShiftOverflow
namespace Counter

/-- **The end of an expensive run.**  Divide `n` by `3` and multiply it by `2`
for as long as it is divisible by three. -/
def postRun (n : ℕ) : ℕ :=
  if h : 0 < n ∧ 3 ∣ n then postRun (2 * n / 3) else n
  decreasing_by
    obtain ⟨hpos, k, rfl⟩ := h
    omega

theorem postRun_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : postRun n = n := by
  rw [postRun]; simp [h]

theorem postRun_zero : postRun 0 = 0 := by rw [postRun]; simp

/-- An expensive step does not change where the run ends. -/
theorem postRun_of_dvd {n : ℕ} (hpos : 0 < n) (h : 3 ∣ n) :
    postRun n = postRun (2 * n / 3) := by
  rw [postRun]; simp [hpos, h]

/-- The closed form of `postRun` on `3 ^ r * s` with `s` prime to three. -/
theorem postRun_pow_mul : ∀ (r s : ℕ), ¬ 3 ∣ s → postRun (3 ^ r * s) = 2 ^ r * s := by
  intro r
  induction r with
  | zero => intro s hs; simpa using postRun_of_not_dvd hs
  | succ r ih =>
      intro s hs
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp at hs
      · have hpos : 0 < 3 ^ (r + 1) * s := by positivity
        have hdvd : (3 : ℕ) ∣ 3 ^ (r + 1) * s := ⟨3 ^ r * s, by ring⟩
        have hhalf : 2 * (3 ^ (r + 1) * s) / 3 = 3 ^ r * (2 * s) := by
          have h : 2 * (3 ^ (r + 1) * s) = 3 * (3 ^ r * (2 * s)) := by ring
          rw [h, Nat.mul_div_cancel_left _ (by norm_num)]
        have h2s : ¬ 3 ∣ 2 * s := by
          intro hc
          exact hs (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hc)
        rw [postRun_of_dvd hpos hdvd, hhalf, ih (2 * s) h2s]
        ring

/-- Every positive `n` is `3 ^ r * s` with `s` prime to three. -/
theorem exists_three_factor : ∀ (n : ℕ), 0 < n → ∃ r s, 0 < s ∧ ¬ 3 ∣ s ∧ n = 3 ^ r * s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases h3 : 3 ∣ n
      · obtain ⟨m, rfl⟩ := h3
        have hm : 0 < m := by omega
        obtain ⟨r, s, hs, hs3, rfl⟩ := ih m (by omega) hm
        exact ⟨r + 1, s, hs, hs3, by ring⟩
      · exact ⟨0, n, hn, h3, by ring⟩

/-- **A long run is expensive.**  The count at the end of an expensive run is
never much smaller than the count at its start: `n ^ 17 ≤ (postRun n) ^ 27`,
the exponents being those of `3 ^ 17 ≤ 2 ^ 27`. -/
theorem pow_le_postRun_pow (n : ℕ) : n ^ 17 ≤ postRun n ^ 27 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [postRun_zero]
  obtain ⟨r, s, hspos, hs, rfl⟩ := exists_three_factor n hn
  rw [postRun_pow_mul r s hs]
  have key : (3 ^ r) ^ 17 * s ^ 17 ≤ (2 ^ r) ^ 27 * s ^ 27 := by
    have h1 : (3 ^ r) ^ 17 ≤ (2 ^ r) ^ 27 := by
      have h : (3 : ℕ) ^ 17 ≤ 2 ^ 27 := by norm_num
      calc (3 ^ r) ^ 17 = (3 ^ 17) ^ r := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2 ^ 27) ^ r := Nat.pow_le_pow_left h r
        _ = (2 ^ r) ^ 27 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h2 : s ^ 17 ≤ s ^ 27 := Nat.pow_le_pow_right hspos (by norm_num)
    exact Nat.mul_le_mul h1 h2
  calc (3 ^ r * s) ^ 17 = (3 ^ r) ^ 17 * s ^ 17 := by rw [Nat.mul_pow]
    _ ≤ (2 ^ r) ^ 27 * s ^ 27 := key
    _ = (2 ^ r * s) ^ 27 := by rw [Nat.mul_pow]

/-- If `postRun n` were small, `n` would be small: the contrapositive form in
which the bound is used. -/
theorem le_postRun {n K : ℕ} (h : K ^ 27 ≤ n ^ 17) : K ≤ postRun n := by
  by_contra hcon
  push_neg at hcon
  have h1 : postRun n ^ 27 < K ^ 27 := Nat.pow_lt_pow_left hcon (by norm_num)
  have h2 := pow_le_postRun_pow n
  omega

theorem postRun_le (n : ℕ) : postRun n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [postRun_zero]
  obtain ⟨r, s, hspos, hs, rfl⟩ := exists_three_factor n hn
  rw [postRun_pow_mul r s hs]
  exact Nat.mul_le_mul_right s (Nat.pow_le_pow_left (by norm_num) r)

end Counter
end ShiftOverflow
