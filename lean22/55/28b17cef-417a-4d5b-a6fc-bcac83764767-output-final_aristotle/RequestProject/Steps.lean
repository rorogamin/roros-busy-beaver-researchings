/-
# One token of the scan

The scan of an epoch meets three kinds of token, and this file names the
arithmetic of each of them and proves the corresponding unfolding rule for
`scan` and for the frontier count `scanT`:

* a **cheap** token `(a, c)` with `c ≠ 3` — a radix-2 position: it leaves a `2`
  behind and passes `chT a t = 2t - hcost a` visits on;
* an **expensive** token `(a, 3)` — a radix-3/2 position: it leaves
  `expD a t ∈ {0, 1, 3}` behind and passes `expT a t ≈ 2t/3` on;
* the **frontier** token `[a]`, the last one: it leaves `frD a t` behind and
  `frT a t` visits run off the end of the word, growing `freshW (frT a t)`.

With these the scan is a three-line recursion and the comparison of two
consecutive epochs (`RequestProject/Lockstep.lean`) can be done token by token
without ever unfolding `scan` again.
-/
import RequestProject.Terminal

namespace ShiftOverflow
namespace Counter

/-! ## The three transfers -/

/-- A cheap token passes on `2t` visits, less what its head eats. -/
def chT (a t : ℕ) : ℕ := 2 * t - hcost a

/-- An expensive token — a radix-3/2 position — passes on about `2t/3`. -/
def expT (a t : ℕ) : ℕ :=
  if a = 2 then cycE (t - 1) 0 else if a = 0 then cycE (t - 1) 1 - 1 else cycE (t - 2) 0

/-- The digit an expensive token leaves behind. -/
def expD (a t : ℕ) : ℕ :=
  if a = 2 then stDigit (cycS (t - 1) 0)
  else if a = 0 then stDigit (cycS (t - 1) 1)
  else stDigit (cycS (t - 2) 0)

/-- The visits that run off the end of the word at the frontier token. -/
def frT (a t : ℕ) : ℕ :=
  if a = 0 then cycE (t - 1) 2 else if a = 1 then cycE (t - 1) 0 else cycE t 0

/-- The digit the frontier token leaves behind. -/
def frD (a t : ℕ) : ℕ :=
  if a = 0 then stDigit (cycS (t - 1) 2)
  else if a = 1 then stDigit (cycS (t - 1) 0)
  else stDigit (cycS t 0)

/-! ## Reading a digit -/

theorem stDigit_eq_three {d : ℕ} : stDigit d = 3 ↔ d % 3 = 1 := by
  unfold stDigit; constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

theorem stDigit_eq_one {d : ℕ} : stDigit d = 1 ↔ d % 3 = 2 := by
  unfold stDigit; constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

theorem stDigit_le_three (d : ℕ) : stDigit d ≤ 3 := by unfold stDigit; split_ifs <;> omega

theorem stDigit_ne_two (d : ℕ) : stDigit d ≠ 2 := by unfold stDigit; split_ifs <;> omega

theorem expD_le_three (a t : ℕ) : expD a t ≤ 3 := by
  unfold expD; split_ifs <;> exact stDigit_le_three _

theorem frD_le_three (a t : ℕ) : frD a t ≤ 3 := by
  unfold frD; split_ifs <;> exact stDigit_le_three _

/-! ## The transfers, head by head -/

theorem expT_head_zero (t : ℕ) : expT 0 t = (t - 1) - (t - 1) / 3 - 1 := by
  unfold expT; simp [cycE_one_eq]

theorem expT_head_one (t : ℕ) : expT 1 t = (t - 2) - (t - 2 + 2) / 3 := by
  unfold expT; simp [cycE_zero_eq]

theorem expT_head_two (t : ℕ) : expT 2 t = (t - 1) - (t - 1 + 2) / 3 := by
  unfold expT; simp [cycE_zero_eq]

theorem frT_head_zero (t : ℕ) : frT 0 t = (t - 1) - (t - 1 + 1) / 3 := by
  unfold frT; simp [cycE_two_eq]

theorem frT_head_one (t : ℕ) : frT 1 t = (t - 1) - (t - 1 + 2) / 3 := by
  unfold frT; simp [cycE_zero_eq]

theorem frT_head_two (t : ℕ) : frT 2 t = t - (t + 2) / 3 := by
  unfold frT; simp [cycE_zero_eq]

theorem frD_head_zero (t : ℕ) : frD 0 t = stDigit ((2 + (t - 1)) % 3) := by
  unfold frD cycS; simp

theorem frD_head_one (t : ℕ) : frD 1 t = stDigit ((t - 1) % 3) := by
  unfold frD cycS; simp

theorem frD_head_two (t : ℕ) : frD 2 t = stDigit (t % 3) := by
  unfold frD cycS; simp

theorem chT_head_zero (t : ℕ) : chT 0 t = 2 * t - 1 := by unfold chT; simp

theorem chT_head_one (t : ℕ) : chT 1 t = 2 * t - 2 := by unfold chT; simp

theorem chT_head_two (t : ℕ) : chT 2 t = 2 * t := by unfold chT; simp

/-! ## Unfolding the scan -/

theorem scan_zero_cons (a : ℕ) (rest : List ℕ) : scan 0 (a :: rest) = none := by
  match rest with
  | [] => simp [scan]
  | _ :: _ => simp [scan]

theorem scanT_zero_cons (a : ℕ) (rest : List ℕ) : scanT 0 (a :: rest) = none := by
  match rest with
  | [] => simp [scanT]
  | _ :: _ => simp [scanT]

/-- The frontier token. -/
theorem scan_last {a t : ℕ} (ha : a ≤ 2) (ht : 1 ≤ t) :
    scan t [a] = some (frD a t :: freshW (frT a t)) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scan, frD, frT, show ¬ t = 0 by omega]

theorem scanT_last {a t : ℕ} (ha : a ≤ 2) (ht : 1 ≤ t) : scanT t [a] = some (frT a t) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scanT, frT, show ¬ t = 0 by omega]

/-- A cheap token. -/
theorem scan_cheap {a c t : ℕ} {rest : List ℕ} (ha : a ≤ 2) (ht : 1 ≤ t) (hc : c ≠ 3) :
    scan t (a :: c :: rest) = (scan (chT a t) (c :: rest)).map (fun o => 2 :: o) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scan, chT, hc, show ¬ t = 0 by omega]

theorem scanT_cheap {a c t : ℕ} {rest : List ℕ} (ha : a ≤ 2) (ht : 1 ≤ t) (hc : c ≠ 3) :
    scanT t (a :: c :: rest) = scanT (chT a t) (c :: rest) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scanT, chT, hc, show ¬ t = 0 by omega]

/-- An expensive token. -/
theorem scan_exp {a t : ℕ} {rest : List ℕ} (ha : a ≤ 2) (ht : 2 ≤ t) :
    scan t (a :: 3 :: rest) = (scan (expT a t) (0 :: rest)).map (fun o => expD a t :: o) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scan, expT, expD, show ¬ t = 0 by omega, show ¬ t < 2 by omega]

theorem scanT_exp {a t : ℕ} {rest : List ℕ} (ha : a ≤ 2) (ht : 2 ≤ t) :
    scanT t (a :: 3 :: rest) = scanT (expT a t) (0 :: rest) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
    simp [scanT, expT, show ¬ t = 0 by omega, show ¬ t < 2 by omega]

/-! ## What a successful scan tells us about its first token -/

theorem scan_head_le {t a : ℕ} {rest : List ℕ} (h : (scan t (a :: rest)).isSome) : a ≤ 2 := by
  by_contra hcon
  match rest with
  | [] =>
      simp only [scan] at h
      split_ifs at h <;> simp_all
  | c :: rest' =>
      simp only [scan] at h
      split_ifs at h <;> simp_all

theorem scan_pos {t a : ℕ} {rest : List ℕ} (h : (scan t (a :: rest)).isSome) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [scan_zero_cons] at h; simp at h
  · exact ht

/-- An expensive token that is not starved has at least two visits: with one
visit a head `0` or `1` writes a `4` that nothing erases, and a head `2` passes
nothing on. -/
theorem scan_exp_pos {t a : ℕ} {rest : List ℕ} (h : (scan t (a :: 3 :: rest)).isSome) :
    2 ≤ t := by
  have ha := scan_head_le h
  have ht := scan_pos h
  by_contra hcon
  have ht1 : t = 1 := by omega
  subst ht1
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
  · simp [scan] at h
  · simp [scan] at h
  · simp only [scan] at h
    simp [cycE_zero_eq, scan_zero_cons] at h

end Counter
end ShiftOverflow
