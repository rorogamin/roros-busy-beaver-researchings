import RequestProject.Price

/-!
# The two-epoch argument: the pair invariant propagates

The lemmas of §§5–8 of the two-epoch argument, and their combination
`good_pair`: if two consecutive overflow chunk words `c` and `T c` satisfy
`Good`, so does the next one, `T (T c)`.
-/

namespace BB25


/-! ## Small facts about powers -/

theorem zpow_le_one_of_nonneg {d : ℤ} (hd : 0 ≤ d) : (2 : ℚ) ^ (-d) ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

theorem zpow_neg_le_quarter {d : ℤ} (hd : 2 ≤ d) : (2 : ℚ) ^ (-d) ≤ 1 / 4 := by
  calc (2 : ℚ) ^ (-d) ≤ 2 ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 4 := by norm_num

theorem z2_mono {a b : ℤ} (h : a ≤ b) : (2 : ℚ) ^ (-b) ≤ 2 ^ (-a) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

/-! ## One and two emissions do not raise the inherited price -/

/-- **Lemma 7.1, with heights.**  Emitting never raises a height, and every
paying position of the emission is an old `B`; walked from a height `h' ≥ h`,
the emission costs at most `2^(-(h'-h))` times the old price. -/
theorem rho_emit : ∀ (cs : List Ck) (R : ℕ) (h h' : ℤ), h ≤ h' →
    rho h' (emitW R cs) ≤ 2 ^ (-(h' - h)) * rho h cs := by
  intro cs
  induction cs with
  | nil => intro R h h' _; simp [rho, emitW]
  | cons c cs ih =>
      intro R h h' hh
      have hf : (0 : ℚ) ≤ 2 ^ (-(h' - h)) := by positivity
      cases c with
      | M =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          have := ih (stepT .M R) (h + 1) (h' + 1) (by omega)
          rwa [show h' + 1 - (h + 1) = h' - h by ring] at this
      | S =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          have := ih (stepT .S R) (h + 1) (h' + 1) (by omega)
          rw [show h' + 1 - (h + 1) = h' - h by ring] at this
          have : (0 : ℚ) ≤ 2 ^ (-(h' - h)) * 2 ^ (-(h + 1)) := by positivity
          nlinarith
      | B =>
          simp only [emitW, emitLabel]
          have hr := rho_nonneg cs (h + -1)
          have hmul : (2 : ℚ) ^ (-(h' - h)) * 2 ^ (-(h + -1)) = 2 ^ (-(h' + -1)) := by
            rw [← z2]; congr 1; ring
          split_ifs with hR
          · simp only [rho, Ck.pays, Ck.wt, ↓reduceIte]
            have h1 := ih (stepT .B R) (h + -1) (h' + 1) (by omega)
            have h2 : (2 : ℚ) ^ (-(h' + 1 - (h + -1))) ≤ 2 ^ (-(h' - h)) := z2_mono (by omega)
            have h3 : (2 : ℚ) ^ (-(h' + 1)) ≤ 2 ^ (-(h' + -1)) := z2_mono (by omega)
            have h4 : (2 : ℚ) ^ (-(h' + 1 - (h + -1))) * rho (h + -1) cs
                ≤ 2 ^ (-(h' - h)) * rho (h + -1) cs := mul_le_mul_of_nonneg_right h2 hr
            rw [mul_add, hmul]
            linarith
          · simp only [rho, Ck.pays, Ck.wt, ↓reduceIte]
            have h1 := ih (stepT .B R) (h + -1) (h' + -1) (by omega)
            rw [show h' + -1 - (h + -1) = h' - h by ring] at h1
            rw [mul_add, hmul]
            linarith

theorem rho_emit_le (cs : List Ck) (R : ℕ) (h : ℤ) : rho h (emitW R cs) ≤ rho h cs := by
  have := rho_emit cs R h h (le_refl _)
  simpa using this

/-- **Lemma 7.2, the inductive form.**  If the second emission enters with an
odd capacity and at a height no lower than the original walk, two emissions
cost at most a quarter of the original price: the first old `B` is converted
by one of the two emissions. -/
theorem rho_emit2 : ∀ (cs : List Ck) (R1 R2 : ℕ) (h h2 : ℤ), R2 % 2 = 1 → h ≤ h2 →
    rho h2 (emitW R2 (emitW R1 cs)) ≤ rho h cs / 4 := by
  intro cs
  induction cs with
  | nil => intro R1 R2 h h2 _ _; simp [rho, emitW]
  | cons c cs ih =>
      intro R1 R2 h h2 hodd hh
      cases c with
      | M =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          exact ih _ _ (h + 1) (h2 + 1) (by simp only [stepT]; omega) (by omega)
      | S =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          have := ih (stepT .S R1) (stepT .M R2) (h + 1) (h2 + 1) (by simp only [stepT]; omega)
            (by omega)
          have : (0 : ℚ) ≤ 2 ^ (-(h + 1)) := by positivity
          linarith
      | B =>
          simp only [emitW, emitLabel]
          have hr := rho_nonneg cs (h + -1)
          have hq : (2 : ℚ) ^ (-(h + 1)) = 2 ^ (-(h + -1)) / 4 := by
            rw [show -(h + -1) = -(h + 1) + 2 by ring, z2]; norm_num
          split_ifs with hR
          · -- converted by the first emission
            simp only [rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
            have h1 := rho_emit (emitW (stepT .B R1) cs) (stepT .S R2) (h + 1) (h2 + 1) (by omega)
            have h1' : (2 : ℚ) ^ (-(h2 + 1 - (h + 1))) ≤ 1 := zpow_le_one_of_nonneg (by omega)
            have hr1 := rho_nonneg (emitW (stepT .B R1) cs) (h + 1)
            have h2' := rho_emit cs (stepT .B R1) (h + -1) (h + 1) (by omega)
            have hq2 : (2 : ℚ) ^ (-(h + 1 - (h + -1))) = 1 / 4 := by
              rw [show -(h + 1 - (h + -1)) = (-2 : ℤ) by ring]; norm_num
            rw [hq2] at h2'
            have : (0 : ℚ) ≤ 2 ^ (-(h + -1)) := by positivity
            nlinarith
          · -- converted by the second emission
            simp only [hodd, ↓reduceIte, rho, Ck.pays, Ck.wt]
            have h1 := rho_emit (emitW (stepT .B R1) cs) (stepT .B R2) (h + -1) (h2 + 1) (by omega)
            have h1' : (2 : ℚ) ^ (-(h2 + 1 - (h + -1))) ≤ 1 / 4 :=
              zpow_neg_le_quarter (by omega)
            have hr1 := rho_nonneg (emitW (stepT .B R1) cs) (h + -1)
            have h2' := rho_emit_le cs (stepT .B R1) (h + -1)
            have h3 : (2 : ℚ) ^ (-(h2 + 1)) ≤ 2 ^ (-(h + 1)) := z2_mono (by omega)
            have : (2 : ℚ) ^ (-(h2 + 1 - (h + -1))) * rho (h + -1) (emitW (stepT .B R1) cs)
                ≤ 1 / 4 * rho (h + -1) (emitW (stepT .B R1) cs) :=
              mul_le_mul_of_nonneg_right h1' hr1
            linarith

/-- **Lemma 7.2.**  For a word whose scan succeeds, two emissions cost at most
a quarter of its price. -/
theorem rho_emit2_top (cs : List Ck) (hc : ckFold 0 cs ≠ none) :
    rho 0 (emitW 0 (emitW 0 cs)) ≤ rho 0 cs / 4 := by
  cases cs with
  | nil => simp [rho, emitW]
  | cons c cs =>
      cases c with
      | M =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          exact rho_emit2 cs _ _ _ _ (by simp [stepT]) (by norm_num)
      | S =>
          simp only [emitW, emitLabel, rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add]
          have := rho_emit2 cs (stepT .S 0) (stepT .M 0) (0 + 1) (0 + 1) (by simp [stepT])
            (le_refl _)
          have : (0 : ℚ) ≤ 2 ^ (-(0 + 1 : ℤ)) := by positivity
          linarith
      | B => exact absurd (by simp [ckFold_cons, ckStep]) hc

/-! ## The price of a newly appended suffix -/

/-- **The suffix bound (20).**  Any word `β` walked from height `h`, together
with its terminal term, costs at most `(3·2^|β| - 2)·2^(-h)`. -/
theorem suffix_bound : ∀ (β : List Ck) (h : ℤ),
    rho h β + 2 ^ (-(h + ctot β)) ≤ (3 * 2 ^ β.length - 2) * 2 ^ (-h) := by
  intro β
  induction β with
  | nil => intro h; simp [rho]; norm_num
  | cons c β ih =>
      intro h
      have ih' := ih (h + c.wt)
      have hw : (2 : ℚ) ^ (-(h + c.wt)) ≤ 2 * 2 ^ (-h) := by
        cases c
        · simp only [Ck.wt]; rw [z2_succ]; have : (0:ℚ) < 2 ^ (-h) := by positivity
          linarith
        · simp only [Ck.wt]; rw [z2_succ]; have : (0:ℚ) < 2 ^ (-h) := by positivity
          linarith
        · simp only [Ck.wt]; rw [z2_pred]
      have hp : (if c.pays then (2 : ℚ) ^ (-(h + c.wt)) else 0) ≤ 2 ^ (-(h + c.wt)) := by
        split_ifs
        · exact le_refl _
        · positivity
      have hpow : (1 : ℚ) ≤ 2 ^ β.length := one_le_pow₀ (by norm_num)
      have e : -(h + ctot (c :: β)) = -(h + c.wt + ctot β) := by simp; ring
      simp only [rho, List.length_cons, pow_succ]
      rw [e]
      have : (3 * 2 ^ β.length - 2 : ℚ) * 2 ^ (-(h + c.wt)) + 2 ^ (-(h + c.wt))
          ≤ (3 * 2 ^ β.length - 1) * (2 * 2 ^ (-h)) := by
        have : (0 : ℚ) ≤ 3 * 2 ^ β.length - 1 := by linarith
        nlinarith
      nlinarith

/-- The suffix bound, at the heights the two-epoch argument meets: a suffix of
length `E - 1` walked from height at least `E + 2k`, `k ≥ 8`, costs at most
`δ = 3/131072`. -/
theorem suffix_small (t E k : ℕ) (h : ℤ) (ht : t + 1 = E) (hk : 8 ≤ k)
    (hh : (E : ℤ) + 2 * k ≤ h) : (3 * 2 ^ t - 2 : ℚ) * 2 ^ (-h) ≤ 3 / 131072 := by
  have h1 : (2 : ℚ) ^ (-h) ≤ 2 ^ (-((E : ℤ) + 16)) := z2_mono (by omega)
  have h2 : (2 : ℚ) ^ (-((E : ℤ) + 16)) = 1 / (2 ^ E * 65536) := by
    rw [zpow_neg, zpow_add₀ two_ne_zero, zpow_natCast]; norm_num
  have h3 : (2 : ℚ) ^ E = 2 * 2 ^ t := by rw [← ht, pow_succ]; ring
  have hpow : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℚ) ≤ 2 ^ (-h) := by positivity
  rw [h2, h3] at h1
  have : (3 * 2 ^ t - 2 : ℚ) * 2 ^ (-h) ≤ (3 * 2 ^ t) * (1 / (2 * 2 ^ t * 65536)) := by
    apply mul_le_mul (by linarith) h1 hpos (by positivity)
  have e : (3 * 2 ^ t : ℚ) * (1 / (2 * 2 ^ t * 65536)) = 3 / 131072 := by
    field_simp; ring
  linarith

/-! ## Scans of runs of a single chunk -/

theorem foldT_replicate_S : ∀ (n R : ℕ), foldT R (List.replicate n Ck.S) = 2 ^ n * R
  | 0, R => by simp [foldT]
  | n + 1, R => by
      rw [List.replicate_succ, foldT, foldT_replicate_S n, stepT, pow_succ]; ring

theorem foldT_replicate_M : ∀ (n R : ℕ), foldT R (List.replicate n Ck.M) + 1 = 2 ^ n * (R + 1)
  | 0, R => by simp [foldT]
  | n + 1, R => by
      rw [List.replicate_succ, foldT, foldT_replicate_M n, stepT, pow_succ]; ring

theorem emitW_replicate_S : ∀ (n R : ℕ), emitW R (List.replicate n Ck.S) = List.replicate n Ck.M
  | 0, R => rfl
  | n + 1, R => by
      rw [List.replicate_succ, emitW, emitW_replicate_S n, emitLabel, List.replicate_succ]

/-! ## Lemma 5.1: the terminal digits -/

/-- **The value of a cheap scan with twelve terminal `S`s.**  Its final height
`E` is at least `13`, the scan succeeds with a value `v` divisible by `4096`,
and `2^E - 2^(E-13) ≤ v`, `v + 5 < 2^E`. -/
theorem terminal_facts (c : List Ck) (hP : Phi c ≤ eps)
    (hS : ∃ p, c = p ++ List.replicate 12 Ck.S) :
    ∃ E z : ℕ, ctot c = E ∧ 13 ≤ E ∧ 2 ^ E = 8192 * z ∧ 1 ≤ z ∧
      ckFold 0 c = some (foldT 0 c) ∧ foldT 0 c % 4096 = 0 ∧
      8191 * z ≤ foldT 0 c ∧ foldT 0 c + 5 < 8192 * z := by
  have hpos : (0 : ℚ) < 2 ^ (-(ctot c)) := by positivity
  have hrho : rho 0 c < eps := by unfold Phi at hP; linarith
  have heps : eps < 1 := by unfold eps; norm_num
  obtain ⟨v, hv, hlo, hhi⟩ := safe_scan c 0 0 (by simp; linarith)
  have hvT : foldT 0 c = v := ckFold_foldT c 0 v hv
  simp only [Nat.cast_zero, zero_add, neg_zero, zpow_zero, mul_one] at hlo hhi
  -- the final height is at least 13
  have he : (13 : ℤ) ≤ ctot c := by
    have h1 : (2 : ℚ) ^ (-(ctot c)) ≤ 2 ^ (-13 : ℤ) := by
      unfold Phi eps at hP; have := rho_nonneg c 0; linarith
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 h1
    omega
  obtain ⟨E, hE⟩ : ∃ E : ℕ, ctot c = E := ⟨(ctot c).toNat, by omega⟩
  have hE13 : 13 ≤ E := by omega
  obtain ⟨z, hz⟩ : ∃ z, 2 ^ E = 8192 * z :=
    ⟨2 ^ (E - 13), by rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, ← pow_add]; congr 1; omega⟩
  have hz1 : 1 ≤ z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h] at hz; simp at hz
    · exact h
  have hEq : (2 : ℚ) ^ (-(ctot c)) = 1 / (8192 * z) := by
    rw [hE, zpow_neg, zpow_natCast]
    have : ((2 ^ E : ℕ) : ℚ) = 8192 * z := by exact_mod_cast hz
    push_cast at this; rw [this]; ring
  have hzpos : (0 : ℚ) < z := by exact_mod_cast hz1
  rw [hEq] at hlo hhi
  have hrho' : rho 0 c ≤ 1 / 8192 - 1 / (8192 * z) := by
    unfold Phi eps at hP; rw [hEq] at hP
    have : (2 : ℚ) ^ (-13 : ℤ) = 1 / 8192 := by norm_num
    linarith
  -- the two bounds on the value
  have hup : (v : ℚ) + 1 ≤ 8192 * z := by
    have := hhi; rw [mul_one_div, div_le_one (by positivity)] at this
    exact this
  have hdown : 8191 * (z : ℚ) ≤ v := by
    have h1 : 1 - rho 0 c ≤ ((v : ℚ) + 1) / (8192 * z) := by
      rw [← mul_one_div]; exact hlo
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : (1 - (1 / 8192 - 1 / (8192 * z))) * (8192 * z) ≤ (1 - rho 0 c) * (8192 * z) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : (1 - (1 / 8192 - 1 / (8192 * (z : ℚ)))) * (8192 * z) = 8191 * z + 1 := by
      field_simp; ring
    linarith
  have hup' : v + 1 ≤ 8192 * z := by exact_mod_cast hup
  have hdown' : 8191 * z ≤ v := by exact_mod_cast hdown
  -- divisibility by 4096
  obtain ⟨p, rfl⟩ := hS
  have hdiv : foldT 0 (p ++ List.replicate 12 Ck.S) % 4096 = 0 := by
    rw [foldT_append, foldT_replicate_S]; simp [Nat.mul_mod_right]
  refine ⟨E, z, hE, hE13, hz, hz1, by rw [hvT]; exact hv, hdiv, by omega, ?_⟩
  rw [hvT] at hdiv ⊢
  omega

/-- A good word's scan succeeds with value at least `3`. -/
theorem good_scan (c : List Ck) (hc : Good c) : ∃ v, ckFold 0 c = some v ∧ 3 ≤ v := by
  obtain ⟨E, z, -, -, -, hz1, hv, -, hlo, -⟩ := terminal_facts c hc.1 hc.2.1
  exact ⟨_, hv, by omega⟩

/-! ## The digits of the new suffix -/

theorem bits_last12 (N t : ℕ) (ht : 12 ≤ t) (hN : N / 2 ^ (t - 12) = 4095) :
    ∃ q, bitsLSB N t = q ++ List.replicate 12 Ck.S := by
  refine ⟨(List.range (t - 12)).map (bitCk N), ?_⟩
  rw [bitsLSB, show t = (t - 12) + 12 by omega, List.range_add, List.map_append,
    show t - 12 + 12 - 12 = t - 12 by omega]
  congr 1
  rw [List.map_map]
  have : ∀ i ∈ List.range 12, (bitCk N ∘ fun x => t - 12 + x) i = Ck.S := by
    intro i hi
    have hi' : i < 12 := List.mem_range.1 hi
    simp only [Function.comp, bitCk, pow_add, ← Nat.div_div_eq_div_mul, hN]
    interval_cases i <;> simp
  rw [List.map_congr_left this, List.map_const', List.length_range]

theorem bits_first12 (N t : ℕ) (ht : 12 ≤ t) (hN : N % 4096 = 5) :
    ∃ q, bitsLSB N t = [Ck.S, Ck.B, Ck.S, Ck.B] ++ List.replicate 8 Ck.B ++ q := by
  refine ⟨(List.range (t - 12)).map (bitCk N ∘ fun x => 12 + x), ?_⟩
  rw [bitsLSB, show t = 12 + (t - 12) by omega, List.range_add, List.map_append, List.map_map,
    show 12 + (t - 12) - 12 = t - 12 by omega]
  congr 1
  have : ∀ i ∈ List.range 12, bitCk N i = bitCk 5 i := by
    intro i hi
    have hi' : i < 12 := List.mem_range.1 hi
    unfold bitCk
    interval_cases i <;> simp <;> omega
  rw [List.map_congr_left this]
  decide

/-! ## Lemma 6.1: eight forced conversions -/

theorem conv_Bs : ∀ (n x : ℕ), (x + 2) % 2 ^ n = 2 ^ n - 1 → 2 ^ (n + 1) ≤ x + 2 →
    n ≤ conv x (List.replicate n Ck.B)
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, x, hmod, hbig => by
      have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      have hp2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      have hodd : x % 2 = 1 := by
        have h1 : (x + 2) % 2 ^ (n + 1) % 2 = (x + 2) % 2 :=
          Nat.mod_mod_of_dvd _ (by rw [hp]; exact Dvd.intro _ rfl)
        rw [hmod] at h1
        omega
      rw [List.replicate_succ, conv, convAt, if_pos hodd, stepT]
      have hx2 : x / 2 - 1 + 2 = (x + 2) / 2 := by omega
      have hmod' : (x / 2 - 1 + 2) % 2 ^ n = 2 ^ n - 1 := by
        rw [hx2, ← Nat.mod_mul_right_div_self, ← hp, hmod]
        omega
      have hbig' : 2 ^ (n + 1) ≤ x / 2 - 1 + 2 := by omega
      have := conv_Bs n (x / 2 - 1) hmod' hbig'
      omega

theorem conv_append_le (cs ds : List Ck) (R : ℕ) : conv (foldT R cs) ds ≤ conv R (cs ++ ds) := by
  rw [conv_append]; omega

theorem conv_prefix_le (cs ds : List Ck) (R : ℕ) : conv R cs ≤ conv R (cs ++ ds) := by
  rw [conv_append]; omega

/-- **Lemma 6.1.**  If `c` ends in twelve `S`s and the new suffix starts with
the digits `S B S B⁹` of a number `≡ 5 (mod 4096)`, the scan of `A(c) ++ β`
has at least eight conversions. -/
theorem conv_forced (p β q : List Ck)
    (hβ : β = [Ck.S, Ck.B, Ck.S, Ck.B] ++ List.replicate 8 Ck.B ++ q) :
    8 ≤ conv 0 (emitW 0 (p ++ List.replicate 12 Ck.S) ++ β) := by
  refine le_trans ?_ (conv_append_le _ _ _)
  rw [emitW_append, emitW_replicate_S, foldT_append]
  set a := foldT (foldT 0 (emitW 0 p)) (List.replicate 12 Ck.M) with ha
  have ha1 : a + 1 = 4096 * (foldT 0 (emitW 0 p) + 1) := by
    rw [ha, foldT_replicate_M]; norm_num
  rw [hβ, List.append_assoc]
  refine le_trans ?_ (conv_append_le _ _ _)
  have hf : foldT a [Ck.S, Ck.B, Ck.S, Ck.B] = a - 2 := by
    simp only [foldT, stepT]; omega
  rw [hf]
  refine le_trans ?_ (conv_prefix_le _ _ _)
  exact conv_Bs 8 (a - 2) (by norm_num; omega) (by norm_num; omega)

/-! ## The epoch map, unfolded -/

/-- The shape of `T c` for a cheap `c` with twelve terminal `S`s: the emission,
followed by a suffix `β` of length `E - 1` (`E` the final height of `c`)
which ends in twelve `S`s and begins with `S B S B⁹`. -/
theorem epochMap_shape (c : List Ck) (hP : Phi c ≤ eps)
    (hS : ∃ p, c = p ++ List.replicate 12 Ck.S) :
    ∃ (E : ℕ) (β : List Ck), ctot c = E ∧ 13 ≤ E ∧ epochMap c = emitW 0 c ++ β ∧
      β.length + 1 = E ∧ (∃ q, β = q ++ List.replicate 12 Ck.S) ∧
      (∃ q, β = [Ck.S, Ck.B, Ck.S, Ck.B] ++ List.replicate 8 Ck.B ++ q) := by
  obtain ⟨E, z, hE, hE13, hz, hz1, -, hdiv, hlo, hhi⟩ := terminal_facts c hP hS
  set v := foldT 0 c
  have hpE1 : 2 ^ (E - 1) = 4096 * z := by
    have : 2 ^ E = 2 * 2 ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hlog : Nat.log 2 (v + 5) = E - 1 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [show E - 1 + 1 = E by omega]; omega
  have hp13 : 2 ^ (E - 1 - 12) = z := by
    have : 2 ^ (E - 1) = 2 ^ (E - 1 - 12) * 4096 := by
      rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, ← pow_add]; congr 1; omega
    omega
  refine ⟨E, bitsLSB (v + 5 - 2 ^ (E - 1)) (E - 1), hE, hE13, ?_, ?_, ?_, ?_⟩
  · rw [epochMap, hlog]
  · rw [bitsLSB, List.length_map, List.length_range]; omega
  · apply bits_last12 _ _ (by omega)
    rw [hp13]
    apply Nat.div_eq_of_lt_le <;> omega
  · apply bits_first12 _ _ (by omega)
    omega

/-! ## Lemma 8.1 and the pair invariant -/

/-- **The two-epoch invariant propagates.**  If two consecutive overflow chunk
words `c` and `T c` are `Good`, so is `T (T c)`. -/
theorem good_pair (c : List Ck) (hc : Good c) (hd : Good (epochMap c)) :
    Good (epochMap (epochMap c)) := by
  obtain ⟨hPc, hSc, hkc⟩ := hc
  obtain ⟨hPd, hSd, hkd⟩ := hd
  obtain ⟨Ec, βc, hEc, -, hdc, hlc, -, -⟩ := epochMap_shape c hPc hSc
  obtain ⟨Ed, βd, hEd, -, hfd, hld, hlastd, hfirstd⟩ := epochMap_shape _ hPd hSd
  set d := epochMap c with hd_def
  refine ⟨?_, ?_, ?_⟩
  · -- the price
    have hscan : ckFold 0 c ≠ none := by
      obtain ⟨v, hv, -⟩ := good_scan c ⟨hPc, hSc, hkc⟩
      rw [hv]; simp
    have hrc : rho 0 c ≤ eps := by
      unfold Phi at hPc; have : (0 : ℚ) < 2 ^ (-(ctot c)) := by positivity
      linarith
    -- split the price of `T d`
    have hsplit : Phi (epochMap d) = rho 0 (emitW 0 d)
        + (rho (ctot (emitW 0 d)) βd + 2 ^ (-(ctot (emitW 0 d) + ctot βd))) := by
      rw [Phi, hfd, rho_append, ctot_append, zero_add]
      ring
    have hemd : emitW 0 d = emitW 0 (emitW 0 c) ++ emitW (foldT 0 (emitW 0 c)) βc := by
      rw [hdc, emitW_append]
    have hsplit2 : rho 0 (emitW 0 d) = rho 0 (emitW 0 (emitW 0 c))
        + rho (ctot (emitW 0 (emitW 0 c))) (emitW (foldT 0 (emitW 0 c)) βc) := by
      rw [hemd, rho_append, zero_add]
    have hA := rho_emit2_top c hscan
    -- the first suffix, re-emitted
    have hB1 := rho_emit βc (foldT 0 (emitW 0 c)) (ctot (emitW 0 c))
      (ctot (emitW 0 (emitW 0 c))) (by rw [ctot_emitW (emitW 0 c)]; omega)
    have hB2 : (2 : ℚ) ^ (-(ctot (emitW 0 (emitW 0 c)) - ctot (emitW 0 c))) ≤ 1 :=
      zpow_le_one_of_nonneg (by rw [ctot_emitW (emitW 0 c)]; omega)
    have hB3 := suffix_bound βc (ctot (emitW 0 c))
    have hB4 := suffix_small βc.length Ec (conv 0 c) (ctot (emitW 0 c)) hlc hkc
      (by rw [ctot_emitW, hEc])
    have hB5 : (0 : ℚ) ≤ 2 ^ (-(ctot (emitW 0 c) + ctot βc)) := by positivity
    have hrB := rho_nonneg βc (ctot (emitW 0 c))
    have hB : rho (ctot (emitW 0 (emitW 0 c))) (emitW (foldT 0 (emitW 0 c)) βc) ≤ 3 / 131072 := by
      have : (2 : ℚ) ^ (-(ctot (emitW 0 (emitW 0 c)) - ctot (emitW 0 c))) *
          rho (ctot (emitW 0 c)) βc ≤ 1 * rho (ctot (emitW 0 c)) βc :=
        mul_le_mul_of_nonneg_right hB2 hrB
      linarith
    -- the second suffix, with the terminal term
    have hC1 := suffix_bound βd (ctot (emitW 0 d))
    have hC2 := suffix_small βd.length Ed (conv 0 d) (ctot (emitW 0 d)) hld hkd
      (by rw [ctot_emitW, hEd])
    rw [hsplit, hsplit2]
    have e : eps = 16 / 131072 := by unfold eps; norm_num
    rw [e] at hrc ⊢
    linarith
  · -- the terminal digits
    obtain ⟨q, hq⟩ := hlastd
    exact ⟨emitW 0 d ++ q, by rw [hfd, hq, List.append_assoc]⟩
  · -- the forced conversions
    obtain ⟨p, hp⟩ := hSd
    obtain ⟨q, hq⟩ := hfirstd
    rw [hfd, hp]
    exact conv_forced p βd q hq

end BB25
