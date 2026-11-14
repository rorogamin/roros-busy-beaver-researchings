import RequestProject.MixedReset

/-!
# The debt transducer (pure arithmetic)

The wide cascade is tracked by a height `h` and a debt `x`; the left capacity is
then exactly `E = 2^h - 1 - x`.  The normalized debt `x / 2^h` is never used as
a fraction: every comparison of normalized debts is stated with the
denominators cleared, so everything below is arithmetic on `Nat` and `Int`.
-/

namespace TM25

open LB RB Hd

/-! ## The height / debt scan -/

/-- Height change of a reset word: `+1` for `V` and `C1`, `-1` for `C`. -/
def hs : List RB → Int
  | [] => 0
  | V :: w => hs w + 1
  | C1 :: w => hs w + 1
  | C :: w => hs w - 1
  | _ :: w => hs w

/-- Final debt of the scan started with debt `x`. -/
def xs : Nat → List RB → Nat
  | x, [] => x
  | x, V :: w => xs (2 * x) w
  | x, C1 :: w => xs (2 * x + 2) w
  | x, C :: w => xs (x / 2 + 3) w
  | x, _ :: w => xs x w

/-- Number of `C` letters read at even debt ("promotions"). -/
def pc : Nat → List RB → Nat
  | _, [] => 0
  | x, V :: w => pc (2 * x) w
  | x, C1 :: w => pc (2 * x + 2) w
  | x, C :: w => (if x % 2 = 0 then 1 else 0) + pc (x / 2 + 3) w
  | x, _ :: w => pc x w

/-- The emitted word (saturation image) computed from the debt. -/
def em : Nat → List RB → List RB
  | _, [] => []
  | x, V :: w => V :: em (2 * x) w
  | x, C1 :: w => V :: em (2 * x + 2) w
  | x, C :: w => (if x % 2 = 0 then C1 else C) :: em (x / 2 + 3) w
  | x, _ :: w => em x w

/-- All letters are `V`, `C` or `C1`. -/
def Letters (w : List RB) : Prop := ∀ c ∈ w, c = V ∨ c = C ∨ c = C1

theorem xs_append (x : Nat) (a b : List RB) : xs x (a ++ b) = xs (xs x a) b := by
  induction a generalizing x with
  | nil => rfl
  | cons c a ih => cases c <;> simp [xs, ih]

theorem hs_append (a b : List RB) : hs (a ++ b) = hs a + hs b := by
  induction a with
  | nil => simp [hs]
  | cons c a ih => cases c <;> simp [hs, ih] <;> omega

theorem pc_append (x : Nat) (a b : List RB) : pc x (a ++ b) = pc x a + pc (xs x a) b := by
  induction a generalizing x with
  | nil => simp [pc, xs]
  | cons c a ih => cases c <;> simp [pc, xs, ih] <;> omega

theorem em_append (x : Nat) (a b : List RB) : em x (a ++ b) = em x a ++ em (xs x a) b := by
  induction a generalizing x with
  | nil => rfl
  | cons c a ih => cases c <;> simp [em, xs, ih]

theorem hs_em (x : Nat) (a : List RB) : hs (em x a) = hs a + 2 * pc x a := by
  induction a generalizing x with
  | nil => simp [em, hs, pc]
  | cons c a ih =>
    cases c with
    | C =>
      by_cases hx : x % 2 = 0 <;> simp [em, hs, pc, hx, ih] <;> omega
    | V => simp [em, hs, pc, ih]; omega
    | C1 => simp [em, hs, pc, ih]; omega
    | G => simp [em, hs, pc, ih]
    | P => simp [em, hs, pc, ih]
    | S => simp [em, hs, pc, ih]
    | Q => simp [em, hs, pc, ih]

theorem letters_em (x : Nat) (a : List RB) : Letters (em x a) := by
  induction a generalizing x with
  | nil => simp [em, Letters]
  | cons c a ih =>
    intro c' hc
    cases c with
    | C =>
      simp only [em, List.mem_cons] at hc
      rcases hc with rfl | hc
      · by_cases hx : x % 2 = 0 <;> simp [hx]
      · exact ih _ c' hc
    | V =>
      simp only [em, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact ih _ c' hc
    | C1 =>
      simp only [em, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact ih _ c' hc
    | G => exact ih x c' hc
    | P => exact ih x c' hc
    | S => exact ih x c' hc
    | Q => exact ih x c' hc

theorem letters_compbits (N d : Nat) : Letters (compbits N d) := by
  induction N generalizing d with
  | zero => simp [compbits, Letters]
  | succ N ih =>
    intro c hc
    simp only [compbits, List.mem_cons] at hc
    rcases hc with rfl | hc
    · by_cases hd : d % 2 = 0 <;> simp [hd]
    · exact ih _ c hc

theorem letters_append {a b : List RB} (ha : Letters a) (hb : Letters b) : Letters (a ++ b) := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact ha c h
  · exact hb c h

/-! ## Normalized debt is nondecreasing

`x / 2^a ≤ xs x w / 2^b` whenever `b = a + hs w`, stated with cleared
denominators. -/

theorem mu_mono : ∀ (w : List RB) (a b x : Nat), (b : Int) = a + hs w →
    x * 2 ^ b ≤ xs x w * 2 ^ a := by
  intro w
  induction w with
  | nil =>
    intro a b x hb
    have : b = a := by simp [hs] at hb; omega
    subst this; exact Nat.le_refl _
  | cons c w ih =>
    intro a b x hb
    cases c with
    | V =>
      have := ih (a + 1) b (2 * x) (by simp [hs] at hb; omega)
      simp only [xs]
      rw [Nat.pow_succ] at this
      exact Nat.le_of_mul_le_mul_left (c := 2) (by grind) (by decide)
    | C1 =>
      have := ih (a + 1) b (2 * x + 2) (by simp [hs] at hb; omega)
      simp only [xs]
      rw [Nat.pow_succ] at this
      exact Nat.le_of_mul_le_mul_left (c := 2) (by grind) (by decide)
    | C =>
      have := ih a (b + 1) (x / 2 + 3) (by simp [hs] at hb; omega)
      simp only [xs]
      rw [Nat.pow_succ] at this
      have hx : x ≤ (x / 2 + 3) * 2 := by omega
      have h2 := Nat.mul_le_mul_right (2 ^ b) hx
      exact Nat.le_trans (by grind) this
    | G => simpa [xs] using ih a b x (by simpa [hs] using hb)
    | P => simpa [xs] using ih a b x (by simpa [hs] using hb)
    | S => simpa [xs] using ih a b x (by simpa [hs] using hb)
    | Q => simpa [xs] using ih a b x (by simpa [hs] using hb)

/-- Cancelling a common positive factor between a debt comparison and a debt
bound. -/
theorem cancel_aux {s X P Q : Nat} (hP : 0 < P) (h1 : s * P ≤ X * Q) (h2 : 256 * X ≤ P) :
    256 * s ≤ Q := by
  have h3 : 256 * s * P ≤ Q * P :=
    calc 256 * s * P = 256 * (s * P) := Nat.mul_assoc _ _ _
      _ ≤ 256 * (X * Q) := Nat.mul_le_mul_left _ h1
      _ = (256 * X) * Q := (Nat.mul_assoc _ _ _).symm
      _ ≤ P * Q := Nat.mul_le_mul_right _ h2
      _ = Q * P := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h3 hP

/-! ## The debt scan computes the cascade -/

/-- **Safe-cascade lemma** (with the exact capacity formula `E + 1 + x = 2^h`).
If the final debt satisfies `256 * debt ≤ 2^height`, the cascade is valid, its
emitted word is `em`, and its final capacity is `2^H - 1 - xs`. -/
theorem cascade_of_debt : ∀ (w : List RB) (h x E H : Nat), Letters w → E + 1 + x = 2 ^ h →
    (H : Int) = h + hs w → 256 * xs x w ≤ 2 ^ H →
    cOK E w = true ∧ cEmit E w = em x w ∧ cCap E w + 1 + xs x w = 2 ^ H := by
  intro w
  induction w with
  | nil =>
    intro h x E H _ hE hH _
    have : H = h := by simp [hs] at hH; omega
    subst this
    exact ⟨rfl, rfl, by simpa [cCap, xs] using hE⟩
  | cons c w ih =>
    intro h x E H hl hE hH hmu
    have hlw : Letters w := fun c' hc' => hl c' (by simp [hc'])
    cases c with
    | V =>
      simp only [xs] at hmu
      obtain ⟨h1, h2, h3⟩ := ih (h + 1) (2 * x) (2 * E + 1) H hlw
        (by rw [Nat.pow_succ]; omega) (by simp [hs] at hH; omega) hmu
      exact ⟨by simpa [cOK] using h1, by simp [cEmit, em, h2], by simpa [cCap, xs] using h3⟩
    | C1 =>
      simp only [xs] at hmu
      have hm := mu_mono w (h + 1) H (2 * x + 2) (by simp [hs] at hH; omega)
      have hb := cancel_aux (Nat.two_pow_pos H) hm hmu
      rw [Nat.pow_succ] at hb
      have hE1 : 1 ≤ E := by omega
      obtain ⟨h1, h2, h3⟩ := ih (h + 1) (2 * x + 2) (2 * E - 1) H hlw
        (by rw [Nat.pow_succ]; omega) (by simp [hs] at hH; omega) hmu
      exact ⟨by simp [cOK, hE1, h1], by simp [cEmit, em, h2], by simpa [cCap, xs] using h3⟩
    | C =>
      simp only [xs] at hmu
      have hm := mu_mono w h (H + 1) (x / 2 + 3) (by simp [hs] at hH; omega)
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm] at hm
      have hb := cancel_aux (Nat.two_pow_pos H) hm hmu
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := by
        rcases Nat.eq_zero_or_pos h with rfl | hpos
        · simp at hb; omega
        · exact ⟨h - 1, by omega⟩
      rw [Nat.pow_succ] at hb hE
      have hE6 : 6 ≤ E := by omega
      obtain ⟨h1, h2, h3⟩ := ih k (x / 2 + 3) ((E - 6) / 2) H hlw (by omega)
        (by simp [hs] at hH; omega) hmu
      refine ⟨by simp [cOK, hE6, h1], ?_, by simpa [cCap, xs] using h3⟩
      have hpar : (E % 2 = 0) ↔ ¬ (x % 2 = 0) := by omega
      simp only [cEmit, em, h2]
      by_cases hx : x % 2 = 0
      · simp [hx, show ¬ E % 2 = 0 from fun h => (hpar.1 h) hx]
      · simp [hx, hpar.2 hx]
    | G => exact absurd (hl RB.G (by simp)) (by simp)
    | P => exact absurd (hl RB.P (by simp)) (by simp)
    | S => exact absurd (hl RB.S (by simp)) (by simp)
    | Q => exact absurd (hl RB.Q (by simp)) (by simp)

/-! ## The emitted prefix attenuates inherited debt -/

/-- Joint invariant of source debt `x`, output debt `y` and promotion count `p`. -/
def Iinv (x y p : Nat) : Prop := (p = 0 ∧ y = 0 ∧ x % 2 = 0) ∨ (1 ≤ p ∧ y ≤ 4 ^ (p - 1) * x)

theorem image_bound : ∀ (a : List RB) (x y p : Nat), Iinv x y p →
    Iinv (xs x a) (xs y (em x a)) (p + pc x a) := by
  intro a
  induction a with
  | nil => intro x y p h; simpa [xs, em, pc] using h
  | cons c a ih =>
    intro x y p hI
    cases c with
    | V =>
      simp only [xs, em, pc]
      apply ih
      rcases hI with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, by omega, by omega⟩
      · right; exact ⟨h1, by grind⟩
    | C1 =>
      simp only [xs, em, pc]
      apply ih
      rcases hI with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, by omega, by omega⟩
      · right; exact ⟨h1, by grind⟩
    | C =>
      simp only [xs, em, pc]
      by_cases hx : x % 2 = 0
      · simp only [hx, if_true, xs]
        rw [show p + (1 + pc (x / 2 + 3) a) = (p + 1) + pc (x / 2 + 3) a by omega]
        apply ih
        right
        refine ⟨by omega, ?_⟩
        simp only [Nat.add_sub_cancel]
        obtain ⟨r, rfl⟩ : ∃ r, x = 2 * r := ⟨x / 2, by omega⟩
        have hr : 2 * r / 2 = r := by omega
        rw [hr]
        rcases hI with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; simp
        · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at h2
          have hm : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by decide)
          rw [Nat.pow_succ]
          grind
      · simp only [hx, if_false, xs, Nat.zero_add]
        apply ih
        right
        rcases hI with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact absurd h3 hx
        · refine ⟨h1, ?_⟩
          obtain ⟨r, rfl⟩ : ∃ r, x = 2 * r + 1 := ⟨x / 2, by omega⟩
          have hr : (2 * r + 1) / 2 = r := by omega
          rw [hr]
          have hm : 1 ≤ 4 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
          generalize 4 ^ (p - 1) = m at hm h2 ⊢
          grind
    | G => simpa [xs, em, pc] using ih x y p hI
    | P => simpa [xs, em, pc] using ih x y p hI
    | S => simpa [xs, em, pc] using ih x y p hI
    | Q => simpa [xs, em, pc] using ih x y p hI

/-! ## Cost of the complemented binary suffix

Reading `compbits N d` adds at most `(8 d + 2) / 2^a` to the normalized debt,
where `a` is the starting height; again with cleared denominators. -/

theorem cost_bound : ∀ (N d a b x : Nat), (b : Int) = a + hs (compbits N d) →
    xs x (compbits N d) * 2 ^ a ≤ (x + 8 * d + 2) * 2 ^ b := by
  intro N
  induction N with
  | zero =>
    intro d a b x hb
    have : b = a := by simp [compbits, hs] at hb; omega
    subst this
    simp only [compbits, xs]
    exact Nat.mul_le_mul_right _ (by omega)
  | succ N ih =>
    intro d a b x hb
    by_cases hd : d % 2 = 0
    · simp only [compbits, hd, if_true, xs] at hb ⊢
      have := ih (d / 2) (a + 1) b (2 * x + 2) (by simp [hs] at hb; omega)
      rw [Nat.pow_succ] at this
      have hle : 2 * x + 2 + 8 * (d / 2) + 2 ≤ 2 * (x + 8 * d + 2) := by omega
      refine Nat.le_of_mul_le_mul_left (c := 2) ?_ (by decide)
      calc 2 * (xs (2 * x + 2) (compbits N (d / 2)) * 2 ^ a)
          = xs (2 * x + 2) (compbits N (d / 2)) * (2 ^ a * 2) := by grind
        _ ≤ (2 * x + 2 + 8 * (d / 2) + 2) * 2 ^ b := this
        _ ≤ (2 * (x + 8 * d + 2)) * 2 ^ b := Nat.mul_le_mul_right _ hle
        _ = 2 * ((x + 8 * d + 2) * 2 ^ b) := Nat.mul_assoc _ _ _
    · simp only [compbits, hd, if_false, xs] at hb ⊢
      have := ih (d / 2) a (b + 1) (x / 2 + 3) (by simp [hs] at hb; omega)
      rw [Nat.pow_succ] at this
      have hle : (x / 2 + 3 + 8 * (d / 2) + 2) * 2 ≤ x + 8 * d + 2 := by omega
      calc xs (x / 2 + 3) (compbits N (d / 2)) * 2 ^ a
          ≤ (x / 2 + 3 + 8 * (d / 2) + 2) * (2 ^ b * 2) := this
        _ = ((x / 2 + 3 + 8 * (d / 2) + 2) * 2) * 2 ^ b := by grind
        _ ≤ (x + 8 * d + 2) * 2 ^ b := Nat.mul_le_mul_right _ hle

/-! ## Facts about complemented digits -/

theorem compbits_add : ∀ (a b d : Nat),
    compbits (a + b) d = compbits a d ++ compbits b (d / 2 ^ a) := by
  intro a
  induction a with
  | zero => intro b d; simp [compbits]
  | succ a ih =>
    intro b d
    rw [show a + 1 + b = (a + b) + 1 by omega, compbits, compbits, ih, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (2 ^ a) 2]
    rfl

theorem compbits_zero : ∀ b, compbits b 0 = List.replicate b C1 := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih => simp [compbits, ih, List.replicate_succ]

theorem compbits_mod : ∀ (k d : Nat), compbits k d = compbits k (d % 2 ^ k) := by
  intro k
  induction k with
  | zero => intro d; rfl
  | succ k ih =>
    intro d
    rw [compbits, compbits, ih (d / 2), ih (d % 2 ^ (k + 1) / 2)]
    have h1 : d % 2 ^ (k + 1) % 2 = d % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have h2 : d / 2 % 2 ^ k = d % 2 ^ (k + 1) / 2 % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [h1, h2]

theorem hs_compbits_ge : ∀ (N d : Nat), -(N : Int) ≤ hs (compbits N d) := by
  intro N
  induction N with
  | zero => intro d; simp [compbits, hs]
  | succ N ih =>
    intro d
    have := ih (d / 2)
    by_cases hd : d % 2 = 0 <;> simp [compbits, hd, hs] <;> omega

theorem xs_rep : ∀ (k x : Nat), xs x (List.replicate k C1) + 2 = (x + 2) * 2 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp [xs]
  | succ k ih =>
    intro x
    rw [List.replicate_succ, xs, ih]
    grind

theorem pc_prom_five (y : Nat) (hy : y % 2 = 0) : 3 ≤ pc y [C, C1, C, C1, C] := by
  simp only [pc, hy, if_true]
  have a1 : (2 * (y / 2 + 3) + 2) % 2 = 0 := by omega
  simp only [a1, if_true]
  have a2 : (2 * ((2 * (y / 2 + 3) + 2) / 2 + 3) + 2) % 2 = 0 := by omega
  simp only [a2, if_true]
  omega

end TM25
