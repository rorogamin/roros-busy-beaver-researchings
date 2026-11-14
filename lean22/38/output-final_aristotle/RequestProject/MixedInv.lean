import RequestProject.MixedArith

/-!
# The closed reset invariant

`Inv w` (for a reset body `w`, the reset being `L < w P Q`):

* every letter is `V`, `C` or `C1`;
* `w` ends in at least six `C1`s;
* at least three promotions (`C` letters read at even debt);
* normalized debt at most `1/256`, i.e. `256 * xs 0 w ≤ 2 ^ hs w`.

`inv_step`: from a reset whose body satisfies `Inv`, the block system makes a
positive, finite, halt-free run to another reset whose body satisfies `Inv`.
-/

namespace TM25

open LB RB Hd

/-- The closed reset invariant on reset bodies. -/
structure Inv (w : List RB) : Prop where
  letters : Letters w
  tail : ∃ v, w = v ++ List.replicate 6 C1
  prom : 3 ≤ pc 0 w
  debt : ∃ H : Nat, (H : Int) = hs w ∧ 256 * xs 0 w ≤ 2 ^ H

/-- **The invariant is closed under exact reset returns.** -/
theorem inv_step (w : List RB) (hw : Inv w) :
    ∃ w', Inv w' ∧ ∃ t, 0 < t ∧ arun t (resetCfg w) = some (resetCfg w') := by
  obtain ⟨hlet, ⟨v, rfl⟩, hprom, ⟨H, hH, hdebt⟩⟩ := hw
  -- write `w = u C1`
  obtain ⟨u, hu⟩ : ∃ u, u = v ++ List.replicate 5 C1 := ⟨_, rfl⟩
  have hwu : v ++ List.replicate 6 C1 = u ++ [C1] := by
    rw [hu, List.append_assoc]; rfl
  rw [hwu] at hlet hprom hdebt hH ⊢
  have hlu : Letters u := fun c hc => hlet c (by simp [hc])
  obtain ⟨z, hz⟩ : ∃ z, z = xs 0 u := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = pc 0 u := ⟨_, rfl⟩
  have hxw : xs 0 (u ++ [C1]) = 2 * z + 2 := by rw [xs_append, ← hz]; rfl
  have hhw : hs (u ++ [C1]) = hs u + 1 := by rw [hs_append]; rfl
  have hpw : pc 0 (u ++ [C1]) = p := by rw [pc_append, ← hp]; simp [pc]
  rw [hpw] at hprom
  rw [hxw] at hdebt
  rw [hhw] at hH
  -- `z ≡ 30 (mod 32)` and `z ≥ 62`
  have hz32 : z + 2 = (xs 0 v + 2) * 32 := by
    rw [hz, hu, xs_append]; exact xs_rep 5 _
  -- the bound `256 (z + 1) ≤ 2^h'` with `h' = hs u`
  obtain ⟨h', rfl⟩ : ∃ h', H = h' + 1 := by
    rcases Nat.eq_zero_or_pos H with rfl | hpos
    · simp at hdebt; omega
    · exact ⟨H - 1, by omega⟩
  rw [Nat.pow_succ] at hdebt
  have hb : 256 * (z + 1) ≤ 2 ^ h' := by omega
  -- the safe cascade on `u`
  obtain ⟨hok, hemit, hcap⟩ :=
    cascade_of_debt u 0 0 0 h' hlu (by decide) (by push_cast at hH; omega) (by rw [← hz]; omega)
  rw [← hz] at hcap
  have hh14 : 14 ≤ h' := by
    apply Classical.byContradiction
    intro hcon
    have : 2 ^ h' ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨N, rfl⟩ : ∃ N, h' = N + 2 := ⟨h' - 2, by omega⟩
  obtain ⟨M, hM⟩ : ∃ M, N = M + 6 := ⟨N - 6, by omega⟩
  have hpowN : 2 ^ (N + 2) = 4 * 2 ^ N := by rw [Nat.pow_add]; omega
  have hpowM : 2 ^ N = 64 * 2 ^ M := by rw [hM, Nat.pow_add]; omega
  obtain ⟨d, hd⟩ : ∃ d, d = z - 9 := ⟨_, rfl⟩
  have hdM : d < 2 ^ M := by omega
  have hdN : d < 2 ^ N := by omega
  have hcap7 : 7 ≤ cCap 0 u := by omega
  have hNd : cCap 0 u + 10 + d = 4 * 2 ^ N := by omega
  obtain ⟨t, ht, hrun⟩ := reset_return u hok hcap7 N d hdN hNd
  refine ⟨cEmit 0 u ++ compbits N d, ?_, t, ht, hrun⟩
  rw [hemit]
  -- the emitted prefix ends in `V`, so its debt is even
  obtain ⟨y, hy⟩ : ∃ y, y = xs 0 (em 0 u) := ⟨_, rfl⟩
  have hyeven : y % 2 = 0 := by
    rw [hy, hu, show List.replicate 5 C1 = List.replicate 4 C1 ++ [C1] from rfl,
      ← List.append_assoc, em_append, xs_append]
    simp [em, xs]
  -- the image bound
  have hI := image_bound u 0 0 0 (Or.inl ⟨rfl, rfl, rfl⟩)
  rw [Nat.zero_add, ← hp, ← hz, ← hy] at hI
  have hyz : y ≤ 4 ^ (p - 1) * z := by
    rcases hI with ⟨h1, _, _⟩ | ⟨_, h2⟩
    · omega
    · exact h2
  have hhem : hs (em 0 u) = hs u + 2 * p := by rw [hs_em, ← hp]
  refine ⟨letters_append (letters_em 0 u) (letters_compbits N d), ?_, ?_, ?_⟩
  · -- six trailing ones
    refine ⟨em 0 u ++ compbits M d, ?_⟩
    rw [hM, compbits_add, Nat.div_eq_of_lt hdM, compbits_zero, List.append_assoc]
  · -- three promotions
    have hN5 : N = 5 + (N - 5) := by omega
    have hd32 : d % 32 = 21 := by omega
    rw [hN5, compbits_add, compbits_mod 5 d, show (2 : Nat) ^ 5 = 32 from rfl, hd32,
      ← List.append_assoc, pc_append, xs_append, ← hy]
    have h5 : compbits 5 21 = [C, C1, C, C1, C] := by decide
    rw [pc_append, h5]
    have h3 : 3 ≤ pc (xs 0 (em 0 u)) [C, C1, C, C1, C] := pc_prom_five _ (hy ▸ hyeven)
    omega
  · -- the debt bound
    have hge := hs_compbits_ge N d
    obtain ⟨H', hH'⟩ : ∃ H' : Nat, (H' : Int) = ((N + 2 + 2 * p : Nat) : Int) + hs (compbits N d) :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨H', by rw [hs_append, hhem, hH']; push_cast at hH ⊢; omega, ?_⟩
    rw [xs_append, ← hy]
    have hcost := cost_bound N d (N + 2 + 2 * p) H' y hH'
    have key : 256 * (y + 8 * d + 2) ≤ 2 ^ (N + 2 + 2 * p) := by
      have h4p : 2 ^ (N + 2 + 2 * p) = 2 ^ (N + 2) * 4 ^ p := by
        rw [Nat.pow_add, Nat.pow_mul]
      obtain ⟨q, hq⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
      have h4 : 4 ^ p = 4 * 4 ^ (p - 1) := by
        rw [hq, show q + 3 - 1 = q + 2 by omega, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
      have hm16 : 16 ≤ 4 ^ (p - 1) := by
        rw [hq, show q + 3 - 1 = q + 2 by omega, Nat.pow_succ, Nat.pow_succ]
        have : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by decide)
        omega
      rw [h4p, h4]
      generalize 4 ^ (p - 1) = m at hm16 hyz ⊢
      have hmz : 16 * z ≤ m * z := Nat.mul_le_mul_right z hm16
      have hz' : y + 8 * d + 2 ≤ (z + 1) * (4 * m) := by grind
      calc 256 * (y + 8 * d + 2) ≤ 256 * ((z + 1) * (4 * m)) := Nat.mul_le_mul_left _ hz'
        _ = (256 * (z + 1)) * (4 * m) := (Nat.mul_assoc _ _ _).symm
        _ ≤ 2 ^ (N + 2) * (4 * m) := Nat.mul_le_mul_right _ hb
    exact cancel_aux (Nat.two_pow_pos _) hcost key

end TM25
