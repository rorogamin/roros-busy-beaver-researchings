/-
# The value and the debt gap of a generated word above its drain buffer

The word the early clean reset of `0RB` rebuilds is

```
  P(t) Y w X^(h+1) chi(x+1) V
```

and the two things Lemma C needs about its middle part `Y w X^(h+1)` are

* **its value**: reading `w` multiplies the credit `a + 2` by `2^(h+1)` at
  least (`gen_rrun_lb`), so after the `h` pops of the buffer the value is still
  at least `4a - 2` (`gen_rrun_buf`) — enough to supply every pop of the scan;

* **its debt gap**: the reverse scan of `w X^h`, entered with a debt `n` the
  value can pay for, either stops inside the word or leaves it with a debt `m`
  that has been divided by sixteen: `16 (m + 1) ≤ n + 4` (`gen_scan_gap`).

Both are inductions over `Gen`.  The gap is what the counter of the checkpoint
below has to pay for in the end, and the factor sixteen is exactly what turns
the bound `n + 4 ≤ 4 (x + 1)` coming out of the drain digits into the
dual-credit hypothesis `2 m + 2 ≤ x`.

The base words are the only real work: `w0 2` and `w0 3` never let the scan
out at all (a pop always leaves an even debt, which the one bit in front of it
stops), while for `w0 r` with `r ≥ 4` the run of zero bits at its right end and
the run of one bits at its left end divide the debt by more than sixteen.
-/
import RequestProject.BB25.Prefix.RB.LemmaA

namespace BB25.Prefix

open BB25

/-! ## Runs of pops -/

/-- A run of `n` pops divides the credit `value + 2` by `2 ^ n`. -/
theorem rrun_Xrun_val : ∀ (n : ℕ) (v : ℤ),
    rrun (List.replicate n .X) v + 2 = (v + 2) / 2 ^ n := by
  intro n
  induction n with
  | zero => intro v; simp
  | succ n ih =>
      intro v
      rw [List.replicate_succ, rrun_cons, rstep_X, ih]
      have h1 : v / 2 - 1 + 2 = (v + 2) / 2 := by omega
      rw [h1, pow_succ, show (2 : ℤ) ^ n * 2 = 2 * 2 ^ n by ring,
        ← Int.ediv_ediv_of_nonneg (by positivity)]

/-! ## The values of the base words -/

theorem rrun_core (A : ℤ) : rrun [RB.V, RB.Y, RB.Y, RB.V, RB.X] A = 8 * A + 2 := by
  simp only [rrun_cons, rrun_nil, rstep_V, rstep_Y, rstep_X]
  omega

theorem rrun_kword_gen (m : ℕ) (a : ℤ) :
    rrun (kword (m + 1)) a = 2 ^ (2 * m + 4) * (a + 1) - 3 * 2 ^ (m + 1) := by
  rw [kword]
  simp only [Nat.add_sub_cancel]
  rw [rrun_append, rrun_append, rrun_replicate_Y, rrun_core, rrun_replicate_V]
  have e1 : (2 : ℤ) ^ (2 * m + 4) = 2 ^ m * (2 ^ (m + 1) * 8) := by
    rw [show 2 * m + 4 = m + (m + 1) + 3 by omega, pow_add, pow_add]
    ring
  have e2 : (3 : ℤ) * 2 ^ (m + 1) = 2 ^ m * 6 := by ring
  rw [e1, e2]
  ring

/-- The value of the base word `w0 (k+4)`. -/
theorem rrun_w0_big (k : ℕ) (a : ℤ) :
    rrun (w0 (k + 4)) a = 2 ^ (2 * k + 7) * (a + 1) - 3 * 2 ^ (k + 2) := by
  rw [w0_big, show k + 2 = (k + 1) + 1 by omega, rrun_cons, rstep_Y,
    rrun_kword_gen (k + 1) (2 * a + 1)]
  have e1 : (2 : ℤ) ^ (2 * k + 7) = 2 ^ (2 * (k + 1) + 4) * 2 := by
    rw [show 2 * (k + 1) + 4 = (2 * k + 7) - 1 by omega]
    rw [show 2 * k + 7 = (2 * k + 6) + 1 by omega]
    simp only [Nat.add_sub_cancel]
    ring
  rw [e1]
  ring

theorem rrun_w0_two (a : ℤ) : rrun (w0 2) a = 8 * a - 2 := by
  rw [w0_two]
  simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V, rstep_X]
  omega

theorem rrun_w0_three (a : ℤ) : rrun (w0 3) a = 64 * a + 54 := by
  rw [w0_three]
  simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V]
  ring

/-! ## The value of a generated word -/

/-- **A generated word of height `h` multiplies the credit by `2 ^ (h+1)`.** -/
theorem gen_rrun_lb : ∀ {w : List RB} {h : ℕ}, Gen w h → ∀ a : ℤ, 0 ≤ a →
    2 ^ (h + 1) * (2 * a) ≤ rrun w a + 2 := by
  intro w h hg
  induction hg with
  | @base r hr =>
      match r, hr with
      | 2, _ =>
          intro a ha
          rw [rrun_w0_two, show h0 2 = 1 from rfl,
            show (2 : ℤ) ^ (1 + 1) = 4 by norm_num]
          omega
      | 3, _ =>
          intro a ha
          rw [rrun_w0_three, show h0 3 = 2 from rfl,
            show (2 : ℤ) ^ (2 + 1) = 8 by norm_num]
          omega
      | (k + 4), _ =>
          intro a ha
          rw [rrun_w0_big, show h0 (k + 4) = 1 by rw [h0, if_neg (by omega)]]
          have hq : (1 : ℤ) ≤ 2 ^ k := one_le_two_pow
          have e1 : (2 : ℤ) ^ (2 * k + 7) = 2 ^ k * 2 ^ k * 128 := by
            rw [show 2 * k + 7 = k + k + 7 by omega, pow_add, pow_add]
            ring
          have e2 : (3 : ℤ) * 2 ^ (k + 2) = 2 ^ k * 12 := by ring
          have hqq : (1 : ℤ) ≤ 2 ^ k * 2 ^ k := by nlinarith
          have hq2 : (2 : ℤ) ^ k ≤ 2 ^ k * 2 ^ k := by nlinarith
          rw [e1, e2, show (2 : ℤ) ^ (1 + 1) = 4 by norm_num]
          nlinarith [mul_nonneg (sub_nonneg.mpr hqq) ha, hq, hqq, hq2]
  | @pre w h _ ih =>
      intro a ha
      rw [rrun_cons, rstep_Y]
      have := ih (2 * a + 1) (by omega)
      have e : (2 : ℤ) ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 := by ring
      have hp : (0 : ℤ) < 2 ^ (h + 1) := by positivity
      nlinarith [this, hp]
  | @mark w h _ ih =>
      intro a ha
      -- the inner word over the buffer of `h` pops, then the zero bit
      rw [rrun_cons, rstep_Y, rrun_append]
      have hbuf : 4 * (2 * a + 1) - 2 ≤ rrun (w ++ List.replicate h RB.X) (2 * a + 1) := by
        have hval := rrun_Xrun_val h (rrun w (2 * a + 1))
        have hih := ih (2 * a + 1) (by omega)
        have hdiv : (2 : ℤ) ^ (h + 1) * (2 * (2 * a + 1)) / 2 ^ h
            ≤ (rrun w (2 * a + 1) + 2) / 2 ^ h :=
          Int.ediv_le_ediv (by positivity) hih
        have hcan : (2 : ℤ) ^ (h + 1) * (2 * (2 * a + 1)) / 2 ^ h = 4 * (2 * a + 1) := by
          rw [show (2 : ℤ) ^ (h + 1) * (2 * (2 * a + 1)) = 2 ^ h * (4 * (2 * a + 1)) by ring,
            Int.mul_ediv_cancel_left _ (by positivity)]
        rw [hcan] at hdiv
        rw [rrun_append]
        omega
      simp only [rrun_cons, rrun_nil, rstep_V]
      rw [show (2 : ℤ) ^ (0 + 1) = 2 by norm_num]
      omega

/-- The value after the buffer of `h` pops. -/
theorem gen_rrun_buf {w : List RB} {h : ℕ} (hg : Gen w h) (a : ℤ) (ha : 0 ≤ a) :
    4 * a - 2 ≤ rrun (w ++ List.replicate h .X) a := by
  have hval := rrun_Xrun_val h (rrun w a)
  have hih := gen_rrun_lb hg a ha
  have hdiv : (2 : ℤ) ^ (h + 1) * (2 * a) / 2 ^ h ≤ (rrun w a + 2) / 2 ^ h :=
    Int.ediv_le_ediv (by positivity) hih
  have hcan : (2 : ℤ) ^ (h + 1) * (2 * a) / 2 ^ h = 4 * a := by
    rw [show (2 : ℤ) ^ (h + 1) * (2 * a) = 2 ^ h * (4 * a) by ring,
      Int.mul_ediv_cancel_left _ (by positivity)]
  rw [hcan] at hdiv
  rw [rrun_append]
  omega

/-- The value after the full buffer of `h + 1` pops. -/
theorem gen_rrun_buf' {w : List RB} {h : ℕ} (hg : Gen w h) (a : ℤ) (ha : 0 ≤ a) :
    2 * a - 2 ≤ rrun (w ++ List.replicate (h + 1) .X) a := by
  have hb := gen_rrun_buf hg a ha
  have hsplit : w ++ List.replicate (h + 1) RB.X
      = (w ++ List.replicate h RB.X) ++ [RB.X] := by
    rw [List.replicate_succ', ← List.append_assoc]
  rw [hsplit, rrun_append]
  simp only [rrun_cons, rrun_nil, rstep_X]
  omega

/-! ## Composing scans -/

/-- **The scan of a concatenation.**  The scan of the right factor, read over
the value the left factor leaves, feeds its exit debt to the scan of the left
factor. -/
theorem Scan_append_of {p : List RB} {a : ℤ} {Q : ℕ → Prop} : ∀ (s : List RB), Digs s →
    ∀ (n : ℕ), Scan s n (rrun p a) (fun m => Scan p m a Q) → Scan (p ++ s) n a Q := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro _ n h; simpa using h
  | append_singleton u b ih =>
      intro hs n h
      obtain ⟨hsu, hb1⟩ := hs.of_append
      have hb : Dig b := hb1 b (by simp)
      rw [← List.append_assoc]
      rcases hb with rfl | rfl | rfl
      · rcases Scan_snoc_Y.mp h with h0 | ⟨h1, h2⟩
        · exact Scan_snoc_Y.mpr (Or.inl h0)
        · exact Scan_snoc_Y.mpr (Or.inr ⟨h1, ih hsu _ h2⟩)
      · rcases Scan_snoc_V.mp h with h0 | ⟨h1, h2⟩
        · exact Scan_snoc_V.mpr (Or.inl h0)
        · exact Scan_snoc_V.mpr (Or.inr ⟨h1, ih hsu _ h2⟩)
      · obtain ⟨hsup, h2⟩ := Scan_snoc_X.mp h
        refine Scan_snoc_X.mpr ⟨?_, ih hsu _ h2⟩
        rw [rrun_append]
        exact hsup

/-- A single one bit: an even debt stops the scan, an odd one is halved. -/
theorem Scan_single_Y {m : ℕ} {a : ℤ} {Q : ℕ → Prop} (h : m % 2 = 1 → Q ((m - 1) / 2)) :
    Scan [RB.Y] m a Q := by
  rw [show [RB.Y] = ([] : List RB) ++ [RB.Y] from rfl]
  refine Scan_snoc_Y.mpr ?_
  by_cases hp : m % 2 = 0
  · exact Or.inl hp
  · exact Or.inr ⟨by omega, by simpa using h (by omega)⟩

/-- **Crossing a run of one bits divides the debt plus one by `2 ^ L`.** -/
theorem scan_Yrun_gap : ∀ (L n j : ℕ) {a : ℤ} {Q : ℕ → Prop}, j ≤ L →
    (∀ α : ℕ, 2 ^ j * (α + 1) ≤ n + 1 → Q α) → Scan (List.replicate L .Y) n a Q := by
  intro L
  induction L with
  | zero =>
      intro n j a Q hj h
      obtain rfl : j = 0 := by omega
      simpa using h n (by simp)
  | succ L ih =>
      intro n j a Q hj h
      rw [List.replicate_succ']
      refine Scan_snoc_Y.mpr ?_
      by_cases hpar : n % 2 = 0
      · exact Or.inl hpar
      · refine Or.inr ⟨by omega, ih ((n - 1) / 2) (j - 1) (by omega) ?_⟩
        intro α hα
        refine h α ?_
        have hp : (2 : ℕ) ^ j ≤ 2 * 2 ^ (j - 1) := by
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · simp
          · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
            have he : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by ring
            simp only [Nat.add_sub_cancel]
            omega
        have h3 : 2 ^ j * (α + 1) ≤ 2 * (2 ^ (j - 1) * (α + 1)) :=
          by calc 2 ^ j * (α + 1) ≤ (2 * 2 ^ (j - 1)) * (α + 1) :=
                Nat.mul_le_mul_right _ hp
            _ = 2 * (2 ^ (j - 1) * (α + 1)) := by ring
        obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (j - 1) * (α + 1) := ⟨_, rfl⟩
        obtain ⟨G, hG⟩ : ∃ G, G = 2 ^ j * (α + 1) := ⟨_, rfl⟩
        rw [← hP] at hα h3
        rw [← hG] at h3 ⊢
        omega

/-- **Crossing a run of zero bits divides the debt by `2 ^ L`.** -/
theorem scan_Vrun_gap : ∀ (L n j : ℕ) {a : ℤ} {Q : ℕ → Prop}, j ≤ L →
    (∀ β : ℕ, 2 ^ j * β ≤ n → Q β) → Scan (List.replicate L .V) n a Q := by
  intro L
  induction L with
  | zero =>
      intro n j a Q hj h
      obtain rfl : j = 0 := by omega
      simpa using h n (by simp)
  | succ L ih =>
      intro n j a Q hj h
      rw [List.replicate_succ']
      refine Scan_snoc_V.mpr ?_
      by_cases hpar : n % 2 = 1
      · exact Or.inl hpar
      · refine Or.inr ⟨by omega, ih (n / 2) (j - 1) (by omega) ?_⟩
        intro β hβ
        refine h β ?_
        have hp : (2 : ℕ) ^ j ≤ 2 * 2 ^ (j - 1) := by
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · simp
          · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
            have he : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by ring
            simp only [Nat.add_sub_cancel]
            omega
        have h3 : 2 ^ j * β ≤ 2 * (2 ^ (j - 1) * β) :=
          by calc 2 ^ j * β ≤ (2 * 2 ^ (j - 1)) * β := Nat.mul_le_mul_right _ hp
            _ = 2 * (2 ^ (j - 1) * β) := by ring
        obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (j - 1) * β := ⟨_, rfl⟩
        obtain ⟨G, hG⟩ : ∃ G, G = 2 ^ j * β := ⟨_, rfl⟩
        rw [← hP] at hβ h3
        rw [← hG] at h3 ⊢
        omega

/-! ## The debt gap of a generated word -/

/-- **The debt gap.**  The reverse scan of a generated word above its buffer,
entered with a debt its value can pay for, either stops inside the word or
leaves it with a debt divided by sixteen. -/
theorem gen_scan_gap : ∀ {w : List RB} {h : ℕ}, Gen w h → ∀ (a : ℤ) (n : ℕ) (Q : ℕ → Prop),
    (n : ℤ) + 4 ≤ 4 * a - 1 → (∀ m : ℕ, 16 * (m + 1) ≤ n + 4 → Q m) →
    Scan (w ++ List.replicate h .X) n a Q := by
  intro w h hg
  induction hg with
  | @base r hr =>
      match r, hr with
      | 2, _ =>
          intro a n Q hn hQ
          have hw : w0 2 ++ List.replicate (h0 2) RB.X
              = ((((([RB.Y] ++ [RB.X]) ++ [RB.Y]) ++ [RB.Y]) ++ [RB.V]) ++ [RB.X]) := by
            rw [w0_two, show h0 2 = 1 from rfl]
            rfl
          have v5 : rrun ((([RB.Y] ++ [RB.X]) ++ [RB.Y]) ++ [RB.Y] ++ [RB.V]) a
              = 8 * a - 2 := by
            simp only [rrun_append, rrun_cons, rrun_nil, rstep_Y, rstep_X, rstep_V]
            omega
          rw [hw]
          refine Scan_snoc_X.mpr ⟨?_, ?_⟩
          · rw [show (([RB.Y] ++ [RB.X]) ++ [RB.Y]) ++ [RB.Y] ++ [RB.V]
              = (((([RB.Y] ++ [RB.X]) ++ [RB.Y]) ++ [RB.Y]) ++ [RB.V]) by simp] at v5
            rw [v5]
            push_cast
            omega
          refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
          refine Scan_snoc_Y.mpr ?_
          by_cases h1 : (2 * n + 4) / 2 % 2 = 0
          · exact Or.inl h1
          refine Or.inr ⟨by omega, ?_⟩
          refine Scan_snoc_Y.mpr ?_
          by_cases h2 : ((2 * n + 4) / 2 - 1) / 2 % 2 = 0
          · exact Or.inl h2
          refine Or.inr ⟨by omega, ?_⟩
          refine Scan_snoc_X.mpr ⟨?_, ?_⟩
          · rw [show rrun [RB.Y] a = 2 * a + 1 from rfl]
            push_cast
            omega
          · rw [show [RB.Y] = ([] : List RB) ++ [RB.Y] from rfl]
            exact Scan_snoc_Y.mpr (Or.inl (by omega))
      | 3, _ =>
          intro a n Q hn hQ
          have hw : w0 3 ++ List.replicate (h0 3) RB.X
              = (((((([RB.Y] ++ [RB.Y]) ++ [RB.V]) ++ [RB.Y]) ++ [RB.Y]) ++ [RB.V])
                  ++ [RB.X]) ++ [RB.X] := by
            rw [w0_three, show h0 3 = 2 from rfl]
            rfl
          have v6 : rrun ((((([RB.Y] ++ [RB.Y]) ++ [RB.V]) ++ [RB.Y]) ++ [RB.Y]) ++ [RB.V]) a
              = 64 * a + 54 := by
            simp only [rrun_append, rrun_cons, rrun_nil, rstep_Y, rstep_V]
            ring
          have v7 : rrun (((((([RB.Y] ++ [RB.Y]) ++ [RB.V]) ++ [RB.Y]) ++ [RB.Y]) ++ [RB.V])
              ++ [RB.X]) a = 32 * a + 26 := by
            rw [rrun_append, v6]
            simp only [rrun_cons, rrun_nil, rstep_X]
            omega
          rw [hw]
          refine Scan_snoc_X.mpr ⟨by rw [v7]; push_cast; omega, ?_⟩
          refine Scan_snoc_X.mpr ⟨by rw [v6]; push_cast; omega, ?_⟩
          refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
          exact Scan_snoc_Y.mpr (Or.inl (by omega))
      | (k + 4), _ =>
          intro a n Q hn hQ
          have ha : (2 : ℤ) ≤ a := by omega
          have hq : (1 : ℤ) ≤ 2 ^ k := one_le_two_pow
          have hqq : (1 : ℤ) ≤ 2 ^ k * 2 ^ k := by nlinarith
          have hq2 : (2 : ℤ) ^ k ≤ 2 ^ k * 2 ^ k := by nlinarith
          have hh : h0 (k + 4) = 1 := by rw [h0, if_neg (by omega)]
          have hw0 : w0 (k + 4)
              = (List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y, RB.V, RB.X])
                  ++ List.replicate (k + 1) RB.V := by
            rw [w0_big, kword, show k + 2 - 1 = k + 1 by omega,
              show List.replicate (k + 3) RB.Y = RB.Y :: List.replicate (k + 2) RB.Y by
                rw [List.replicate_succ]]
            simp
          -- the value of the whole base word
          have vtot : rrun ((List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y, RB.V, RB.X])
              ++ List.replicate (k + 1) RB.V) a
              = 2 ^ k * 2 ^ k * 128 * (a + 1) - 2 ^ k * 12 := by
            rw [← hw0, rrun_w0_big]
            have e1 : (2 : ℤ) ^ (2 * k + 7) = 2 ^ k * 2 ^ k * 128 := by
              rw [show 2 * k + 7 = k + k + 7 by omega, pow_add, pow_add]
              ring
            have e2 : (3 : ℤ) * 2 ^ (k + 2) = 2 ^ k * 12 := by ring
            rw [e1, e2]
          -- the value in front of the pop of the base word
          have vmid : rrun (List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y]) a
              = 2 ^ k * 64 * (a + 1) - 5 := by
            rw [rrun_append, rrun_replicate_Y]
            simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V]
            have e : (2 : ℤ) ^ (k + 3) = 2 ^ k * 8 := by ring
            rw [e]
            ring
          have vmid4 : rrun ((List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y]) ++ [RB.V]) a
              = 2 ^ k * 128 * (a + 1) - 10 := by
            rw [rrun_append, vmid]
            simp only [rrun_cons, rrun_nil, rstep_V]
            ring
          rw [hh, show List.replicate 1 RB.X = [RB.X] from rfl, hw0]
          refine Scan_snoc_X.mpr ⟨?_, ?_⟩
          · rw [vtot]
            push_cast
            nlinarith [mul_nonneg (sub_nonneg.mpr hqq) (show (0 : ℤ) ≤ a by omega), hq, hqq, hq2]
          -- the run of zero bits at the right end of the base word
          refine Scan_append_of _ (digs_replicate_V _) _ ?_
          refine scan_Vrun_gap (k + 1) (2 * n + 4) 1 (by omega) ?_
          intro β hβ
          rw [pow_one] at hβ
          -- the pop inside the base word
          rw [show List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y, RB.V, RB.X]
            = ((List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y]) ++ [RB.V]) ++ [RB.X] by simp]
          refine Scan_snoc_X.mpr ⟨?_, ?_⟩
          · rw [vmid4]
            push_cast
            nlinarith [mul_le_mul_of_nonneg_right hq (show (0 : ℤ) ≤ a + 1 by omega)]
          -- the zero bit, the two one bits and the zero bit of the core
          refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
          rw [show List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y, RB.Y]
            = ((List.replicate (k + 3) RB.Y ++ [RB.V]) ++ [RB.Y]) ++ [RB.Y] by simp]
          refine Scan_snoc_Y.mpr ?_
          by_cases h1 : (2 * β + 4) / 2 % 2 = 0
          · exact Or.inl h1
          refine Or.inr ⟨by omega, ?_⟩
          refine Scan_snoc_Y.mpr ?_
          by_cases h2 : ((2 * β + 4) / 2 - 1) / 2 % 2 = 0
          · exact Or.inl h2
          refine Or.inr ⟨by omega, ?_⟩
          refine Scan_snoc_V.mpr ?_
          by_cases h3 : (((2 * β + 4) / 2 - 1) / 2 - 1) / 2 % 2 = 1
          · exact Or.inl h3
          refine Or.inr ⟨by omega, ?_⟩
          -- the leading run of one bits
          refine scan_Yrun_gap (k + 3) _ 3 (by omega) ?_
          intro α hα
          refine hQ α ?_
          rw [show (2 : ℕ) ^ 3 = 8 from rfl] at hα
          omega
  | @pre w h hgw ih =>
      intro a n Q hn hQ
      have ha : (2 : ℤ) ≤ a := by omega
      have hsplit : (RB.Y :: w) ++ List.replicate (h + 1) RB.X
          = ([RB.Y] ++ (w ++ List.replicate h RB.X)) ++ [RB.X] := by
        rw [List.replicate_succ']
        simp
      rw [hsplit]
      refine Scan_snoc_X.mpr ⟨?_, ?_⟩
      · have hb := gen_rrun_buf hgw (2 * a + 1) (by omega)
        rw [rrun_append, show rrun [RB.Y] a = 2 * a + 1 from rfl]
        push_cast
        omega
      · refine Scan_append_of _ (hgw.digs.append (digs_Xrun h)) _ ?_
        rw [show rrun [RB.Y] a = 2 * a + 1 from rfl]
        refine ih (2 * a + 1) (2 * n + 4) _ (by push_cast; omega) ?_
        intro m hm
        exact Scan_single_Y (fun _ => hQ _ (by omega))
  | @mark w h hgw ih =>
      intro a n Q hn hQ
      have ha : (2 : ℤ) ≤ a := by omega
      have hsplit : (RB.Y :: (w ++ List.replicate h RB.X ++ [RB.V]))
            ++ List.replicate 0 RB.X
          = ([RB.Y] ++ (w ++ List.replicate h RB.X)) ++ [RB.V] := by
        simp
      rw [hsplit]
      refine Scan_snoc_V.mpr ?_
      by_cases hpar : n % 2 = 1
      · exact Or.inl hpar
      refine Or.inr ⟨by omega, ?_⟩
      refine Scan_append_of _ (hgw.digs.append (digs_Xrun h)) _ ?_
      rw [show rrun [RB.Y] a = 2 * a + 1 from rfl]
      refine ih (2 * a + 1) (n / 2) _ (by push_cast; omega) ?_
      intro m hm
      exact Scan_single_Y (fun _ => hQ _ (by omega))

end BB25.Prefix
