/-
# `0LB`: the arithmetic of one return

Word-level facts used by the return theorem of `0LB`:

* the digits `chi m` of the drain are pops `X`/`V`, and there are at most `s`
  of them when `m < 2^(s+1)` (`chi_length_le`);
* the energy of the clock buffer `Y^r V X^(r-1)` is `e ↦ 4e - 2` for `r ≥ 4`
  (`erun_buffer`);
* a word of `t` pops needs at most `6 (2^t - 1)` initial energy
  (`erun_pops_nonneg`);
* the two density bounds of Corollary 3.2 of the submitted argument for a
  word `YYY v`, `v` a Dyck prefix (`density_bounds`).
-/
import RequestProject.BB25.Prefix.LB0.Energy

namespace BB25.Prefix

open BB25

/-- A word made of pops only. -/
def Pops (t : List RB) : Prop := ∀ b ∈ t, b = RB.X ∨ b = RB.V

theorem Pops.digs {t : List RB} (h : Pops t) : Digs t := by
  intro b hb
  rcases h b hb with rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)

theorem Pops.of_append {t u : List RB} (h : Pops (t ++ u)) : Pops t ∧ Pops u :=
  ⟨fun b hb => h b (by simp [hb]), fun b hb => h b (by simp [hb])⟩

/-! ## The drain digits -/

theorem chi_pops : ∀ m : ℕ, Pops (chi m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro b hb
      by_cases h2 : 2 ≤ m
      · rw [chi_of_le h2] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · split_ifs <;> simp
        · exact ih (m / 2) (by omega) b hb'
      · rw [chi_of_lt (by omega)] at hb
        simp at hb

theorem chi_length_le : ∀ (s m : ℕ), 1 ≤ m → m < 2 ^ (s + 1) → (chi m).length ≤ s := by
  intro s
  induction s with
  | zero =>
      intro m h1 h2
      rw [chi_of_lt (by simpa using h2)]
      simp
  | succ s ih =>
      intro m h1 h2
      by_cases hm : 2 ≤ m
      · rw [chi_of_le hm, List.length_cons]
        have : (chi (m / 2)).length ≤ s := ih (m / 2) (by omega) (by
          rw [pow_succ] at h2
          omega)
        omega
      · rw [chi_of_lt (by omega)]
        simp

/-! ## The energy of the clock buffer -/

theorem erun_replicate_Y (n : ℕ) (e : ℤ) :
    erun (List.replicate n RB.Y) e = 2 ^ n * (e + 1) - 1 := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, erun_cons, ih, estep_Y]
      ring

theorem erun_replicate_X (n : ℕ) (x : ℤ) :
    erun (List.replicate n RB.X) x = (x + 6) / 2 ^ n - 6 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, erun_cons, ih, estep_X, pow_succ]
      have h1 : x / 2 - 3 + 6 = (x + 6) / 2 := by omega
      rw [h1, Int.ediv_ediv_of_nonneg (by norm_num), mul_comm]

/-- **The energy of the clock buffer.** -/
theorem erun_buffer {r : ℕ} (hr : 4 ≤ r) (e : ℤ) :
    erun (List.replicate r RB.Y ++ [RB.V] ++ List.replicate (r - 1) RB.X) e = 4 * e - 2 := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 4 := ⟨r - 4, by omega⟩
  rw [erun_append, erun_append, erun_replicate_Y, erun_singleton, estep_V,
    erun_replicate_X, show p + 4 - 1 = p + 3 by omega]
  have hP : (0 : ℤ) < 2 ^ (p + 3) := by positivity
  have h8 : (8 : ℤ) ≤ 2 ^ (p + 3) := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (p + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsplit : 2 * (2 ^ (p + 4) * (e + 1) - 1) + 6 = 4 * (e + 1) * 2 ^ (p + 3) + 4 := by
    rw [pow_succ]; ring
  rw [hsplit, Int.add_ediv_of_dvd_left (Dvd.intro_left _ rfl),
    Int.mul_ediv_cancel _ (ne_of_gt hP), Int.ediv_eq_zero_of_lt (by norm_num) (by omega)]
  ring

/-- **A word of `t` pops needs at most `6 (2^t - 1)` initial energy.** -/
theorem erun_pops_nonneg : ∀ (t : List RB), Pops t → ∀ e : ℤ,
    6 * (2 ^ t.length - 1) ≤ e → 0 ≤ erun t e := by
  intro t
  induction t with
  | nil => intro _ e he; simpa using he
  | cons b t ih =>
      intro hp e he
      have hb := hp b (by simp)
      have hpt : Pops t := fun c hc => hp c (by simp [hc])
      rw [List.length_cons, pow_succ] at he
      have hpos : (1 : ℤ) ≤ 2 ^ t.length := by
        have : (0 : ℤ) < 2 ^ t.length := by positivity
        omega
      rw [erun_cons]
      refine ih hpt _ ?_
      rcases hb with rfl | rfl
      · simp only [estep_X]
        omega
      · simp only [estep_V]
        omega

/-! ## The two density bounds -/

/-- **The two density bounds of a protected word** (Corollary 3.2). -/
theorem density_bounds {v : List RB} (hv : Digs v) (hd : DyckPre v) {L : ℕ}
    (hL : bal ([RB.Y, RB.Y, RB.Y] ++ v) = (L : ℤ)) :
    23 * 2 ^ (L + 2 * qcnt ([RB.Y, RB.Y, RB.Y] ++ v) 0) + 2 ^ L
        ≤ 24 * (trun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 + 1) ∧
      19 * 2 ^ (L + 2 * qcnt ([RB.Y, RB.Y, RB.Y] ++ v) 0) + 5 * 2 ^ L
        ≤ 24 * (etrun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 + 1) := by
  have hbv : bal v = ((L - 3 : ℕ) : ℤ) := by
    rw [bal_append] at hL
    have h0 := hd.bal_nonneg
    simp at hL
    omega
  have hL3 : 3 ≤ L := by
    rw [bal_append] at hL
    have h0 := hd.bal_nonneg
    simp at hL
    omega
  have hq : qcnt ([RB.Y, RB.Y, RB.Y] ++ v) 0 = qcnt v 7 := by
    rw [qcnt_append]; simp
  have ht : trun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 = trun v 7 7 := by
    rw [trun_append]; simp [qout]
  have he : etrun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 = etrun v 7 7 := by
    rw [etrun_append]; simp [qout]
  rw [hq, ht, he]
  set q := qcnt v 7 with hqdef
  have A := trun_ge_qgain hv hd hbv (a := 7) (c := 7) (by norm_num) (q := q) le_rfl
  have B := etrun_ge_egain hv hd hbv (a := 7) (e := 7) (by norm_num) (q := q) le_rfl
  have h3 := three_qloss q
  have hpowL : (2 : ℤ) ^ L = 8 * 2 ^ (L - 3) := by
    rw [show L = (L - 3) + 3 by omega, pow_add]
    simp only [show L - 3 + 3 - 3 = L - 3 by omega]
    ring
  have hpowLq : (2 : ℤ) ^ (L + 2 * q) = 8 * 2 ^ (L - 3) * 4 ^ q := by
    rw [pow_add, hpowL, pow_mul]
    norm_num
  simp only [qgain, egain] at A B
  rw [hpowLq, hpowL]
  set P : ℤ := 2 ^ (L - 3) with hP
  set F : ℤ := 4 ^ q with hF
  set Q : ℤ := qloss q with hQ
  have h4 : 3 * (P * Q) = P * F - P := by linear_combination P * h3
  constructor
  · linarith [A]
  · linarith [B]

end BB25.Prefix
