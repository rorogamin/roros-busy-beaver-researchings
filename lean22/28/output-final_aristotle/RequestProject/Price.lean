import RequestProject.Chunks

/-!
# The two-epoch argument: the pure chunk-word part

This file formalizes the combinatorial half of the two-epoch non-halting
argument for `1RB3LA3LA0RB2LB_2LA4LA4RA2RA---`: the emission `A(c)` of a chunk
scan, the exact overflow-to-overflow map `T(c) = A(c) ++ β`, the carry-price
potential `Φ`, and the fact that the invariant `Good` on two consecutive
chunk words propagates (`good_pair`).

Nothing here talks about the machine; the connection with the machine is in
`RequestProject/Epoch.lean`.
-/

namespace BB25


/-! ## Total versions of the capacity scan, the emission and the conversions -/

/-- One chunk of the capacity scan, as a total function (truncated subtraction). -/
def stepT : Ck → ℕ → ℕ
  | .M, R => 2 * R + 1
  | .S, R => 2 * R
  | .B, R => R / 2 - 1

/-- The capacity scan, as a total function. -/
def foldT : ℕ → List Ck → ℕ
  | R, [] => R
  | R, c :: cs => foldT (stepT c R) cs

/-- The chunk the rebuilt-and-drained word carries at the place of a chunk
entered with capacity `R`: `M`, `S` give `M`; a `B` gives `S` when entered with
an odd capacity (a *conversion*), `B` otherwise. -/
def emitLabel : Ck → ℕ → Ck
  | .M, _ => .M
  | .S, _ => .M
  | .B, R => if R % 2 = 1 then .S else .B

/-- The emission `A` of a scan started at capacity `R`. -/
def emitW : ℕ → List Ck → List Ck
  | _, [] => []
  | R, c :: cs => emitLabel c R :: emitW (stepT c R) cs

/-- Is the chunk a conversion (a `B` entered with odd capacity)? -/
def convAt : Ck → ℕ → ℕ
  | .B, R => if R % 2 = 1 then 1 else 0
  | _, _ => 0

/-- The number `k` of conversions of a scan started at capacity `R`. -/
def conv : ℕ → List Ck → ℕ
  | _, [] => 0
  | R, c :: cs => convAt c R + conv (stepT c R) cs

/-- The `i`-th binary digit of `N` as a chunk: `S` for `1`, `B` for `0`. -/
def bitCk (N i : ℕ) : Ck := if N / 2 ^ i % 2 = 1 then .S else .B

/-- The low `t` binary digits of `N`, least significant first. -/
def bitsLSB (N t : ℕ) : List Ck := (List.range t).map (bitCk N)

/-- **The overflow-to-overflow map** `T(c) = A(c) ++ β_t(v + 5)`, where `v` is
the value of the scan of `c`, `t = ⌊log₂ (v+5)⌋`, and `β_t` lists the low `t`
bits (the leading `1` of `v + 5` omitted), least significant first. -/
def epochMap (cs : List Ck) : List Ck :=
  emitW 0 cs ++ bitsLSB (foldT 0 cs + 5 - 2 ^ Nat.log 2 (foldT 0 cs + 5))
    (Nat.log 2 (foldT 0 cs + 5))

/-! ## The price -/

/-- **The inherited carry price** `ρ` of a chunk word walked from height `h`:
every paying chunk (`S`, `B`) costs `2^(-height after it)`. -/
def rho : ℤ → List Ck → ℚ
  | _, [] => 0
  | h, c :: cs => (if c.pays then (2 : ℚ) ^ (-(h + c.wt)) else 0) + rho (h + c.wt) cs

/-- **The potential** `Φ = ρ + 2^(-final height)`. -/
def Phi (cs : List Ck) : ℚ := rho 0 cs + (2 : ℚ) ^ (-(ctot cs))

/-- The threshold `ε = 2^(-13)`. -/
def eps : ℚ := (2 : ℚ) ^ (-13 : ℤ)

/-- **The invariant on one overflow chunk word**: cheap, twelve terminal `S`s,
at least eight conversions. -/
def Good (cs : List Ck) : Prop :=
  Phi cs ≤ eps ∧ (∃ p, cs = p ++ List.replicate 12 Ck.S) ∧ 8 ≤ conv 0 cs

/-! ## Bookkeeping -/

theorem foldT_append : ∀ (cs ds : List Ck) (R : ℕ), foldT R (cs ++ ds) = foldT (foldT R cs) ds
  | [], _, _ => rfl
  | c :: cs, ds, R => foldT_append cs ds (stepT c R)

theorem emitW_append : ∀ (cs ds : List Ck) (R : ℕ),
    emitW R (cs ++ ds) = emitW R cs ++ emitW (foldT R cs) ds
  | [], _, _ => rfl
  | c :: cs, ds, R => by
      simp only [List.cons_append, emitW, foldT]
      rw [emitW_append cs ds (stepT c R)]

theorem conv_append : ∀ (cs ds : List Ck) (R : ℕ),
    conv R (cs ++ ds) = conv R cs + conv (foldT R cs) ds
  | [], _, _ => by simp [conv, foldT]
  | c :: cs, ds, R => by
      simp only [List.cons_append, conv, foldT]
      rw [conv_append cs ds (stepT c R)]
      ring

theorem rho_append : ∀ (cs ds : List Ck) (h : ℤ),
    rho h (cs ++ ds) = rho h cs + rho (h + ctot cs) ds
  | [], _, _ => by simp [rho]
  | c :: cs, ds, h => by
      simp only [List.cons_append, rho, ctot_cons]
      rw [rho_append cs ds (h + c.wt), add_assoc, add_assoc]

theorem ctot_emitW : ∀ (cs : List Ck) (R : ℕ),
    ctot (emitW R cs) = ctot cs + 2 * (conv R cs : ℤ)
  | [], _ => by simp [emitW, conv]
  | c :: cs, R => by
      simp only [emitW, conv, ctot_cons, ctot_emitW cs]
      cases c
      · simp only [emitLabel, convAt, Ck.wt]; push_cast; ring
      · simp only [emitLabel, convAt, Ck.wt]; push_cast; ring
      · simp only [emitLabel, convAt]
        split_ifs <;> simp only [Ck.wt] <;> push_cast <;> ring

theorem ckFold_foldT : ∀ (cs : List Ck) (R v : ℕ), ckFold R cs = some v → foldT R cs = v
  | [], R, v, h => by simpa [foldT] using h
  | c :: cs, R, v, h => by
      rw [ckFold_cons] at h
      cases hs : ckStep c R with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some R' =>
          rw [hs] at h
          have : stepT c R = R' := by
            cases c <;> simp only [ckStep, stepT, Option.some.injEq] at hs ⊢ <;> try exact hs
            split at hs
            · exact absurd hs (by simp)
            · simpa using hs
          simp only [foldT, this]
          exact ckFold_foldT cs R' v h

theorem rho_nonneg : ∀ (cs : List Ck) (h : ℤ), 0 ≤ rho h cs
  | [], _ => le_refl _
  | c :: cs, h => by
      simp only [rho]
      have := rho_nonneg cs (h + c.wt)
      split_ifs <;> positivity

theorem z2 (a b : ℤ) : (2 : ℚ) ^ (a + b) = 2 ^ a * 2 ^ b := zpow_add₀ two_ne_zero a b

theorem z2_succ (h : ℤ) : (2 : ℚ) ^ (-(h + 1)) = 2 ^ (-h) / 2 := by
  rw [show -(h + 1) = -h + (-1) by ring, z2, zpow_neg_one]; ring

theorem z2_pred (h : ℤ) : (2 : ℚ) ^ (-(h + -1)) = 2 * 2 ^ (-h) := by
  rw [show -(h + -1) = -h + 1 by ring, z2, zpow_one]; ring

/-! ## Cheap words are safe -/

/-- **Lemma 4.1.**  Along a scan, `(R+1)·2^(-h)` decreases by at most the
price paid, and never increases.  A scan whose price is below that quantity
therefore never fails. -/
theorem safe_scan : ∀ (cs : List Ck) (R : ℕ) (h : ℤ),
    rho h cs < ((R : ℚ) + 1) * 2 ^ (-h) →
    ∃ v, ckFold R cs = some v ∧
      ((R : ℚ) + 1) * 2 ^ (-h) - rho h cs ≤ ((v : ℚ) + 1) * 2 ^ (-(h + ctot cs)) ∧
      ((v : ℚ) + 1) * 2 ^ (-(h + ctot cs)) ≤ ((R : ℚ) + 1) * 2 ^ (-h) := by
  intro cs
  induction cs with
  | nil => intro R h _; exact ⟨R, rfl, by simp [rho], by simp⟩
  | cons c cs ih =>
      intro R h hlt
      have hx : (0 : ℚ) < 2 ^ (-h) := by positivity
      cases c with
      | M =>
          simp only [rho, Ck.pays, Ck.wt, Bool.false_eq_true, ↓reduceIte, zero_add] at hlt ⊢
          have hQ : (((2 * R + 1 : ℕ) : ℚ) + 1) * 2 ^ (-(h + 1)) = ((R : ℚ) + 1) * 2 ^ (-h) := by
            rw [z2_succ]; push_cast; ring
          obtain ⟨v, hv, h1, h2⟩ := ih (2 * R + 1) (h + 1) (by rw [hQ]; exact hlt)
          refine ⟨v, by rw [ckFold_cons]; exact hv, ?_, ?_⟩
          · rw [ctot_cons, Ck.wt, ← add_assoc, ← hQ]; exact h1
          · rw [ctot_cons, Ck.wt, ← add_assoc, ← hQ]; exact h2
      | S =>
          simp only [rho, Ck.pays, Ck.wt, ↓reduceIte] at hlt ⊢
          have hQ : (((2 * R : ℕ) : ℚ) + 1) * 2 ^ (-(h + 1))
              = ((R : ℚ) + 1) * 2 ^ (-h) - 2 ^ (-(h + 1)) := by
            rw [z2_succ]; push_cast; ring
          have hp : (0 : ℚ) ≤ 2 ^ (-(h + 1)) := by positivity
          obtain ⟨v, hv, h1, h2⟩ := ih (2 * R) (h + 1) (by rw [hQ]; linarith)
          refine ⟨v, by rw [ckFold_cons]; exact hv, ?_, ?_⟩
          · rw [ctot_cons, Ck.wt, ← add_assoc]; rw [hQ] at h1; linarith
          · rw [ctot_cons, Ck.wt, ← add_assoc]; rw [hQ] at h2; linarith
      | B =>
          simp only [rho, Ck.pays, Ck.wt, ↓reduceIte] at hlt ⊢
          have hp : (2 : ℚ) ^ (-(h + -1)) = 2 * 2 ^ (-h) := z2_pred h
          have hr := rho_nonneg cs (h + -1)
          by_cases hR : R / 2 = 0
          · exfalso
            have hR1 : R ≤ 1 := by omega
            have : ((R : ℚ) + 1) ≤ 2 := by
              have : (R : ℚ) ≤ 1 := by exact_mod_cast hR1
              linarith
            rw [hp] at hlt
            nlinarith
          · have hR2 : 1 ≤ R / 2 := Nat.one_le_iff_ne_zero.2 hR
            have hdiv : R ≤ 2 * (R / 2) + 1 := by omega
            have hdiv' : 2 * (R / 2) ≤ R := Nat.mul_div_le R 2
            have hQ : (((R / 2 - 1 : ℕ) : ℚ) + 1) * 2 ^ (-(h + -1))
                = 2 * ((R / 2 : ℕ) : ℚ) * 2 ^ (-h) := by
              rw [hp, Nat.cast_sub hR2]; push_cast; ring
            have hlo : ((R : ℚ) + 1) * 2 ^ (-h) - 2 ^ (-(h + -1))
                ≤ 2 * ((R / 2 : ℕ) : ℚ) * 2 ^ (-h) := by
              rw [hp]
              have : (R : ℚ) ≤ 2 * ((R / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hdiv
              nlinarith
            have hhi : 2 * ((R / 2 : ℕ) : ℚ) * 2 ^ (-h) ≤ ((R : ℚ) + 1) * 2 ^ (-h) := by
              have : 2 * ((R / 2 : ℕ) : ℚ) ≤ (R : ℚ) := by exact_mod_cast hdiv'
              nlinarith
            obtain ⟨v, hv, h1, h2⟩ := ih (R / 2 - 1) (h + -1) (by rw [hQ]; linarith)
            refine ⟨v, ?_, ?_, ?_⟩
            · rw [ckFold_cons, ckStep, if_neg hR]; exact hv
            · rw [ctot_cons, Ck.wt, ← add_assoc]; rw [hQ] at h1; linarith
            · rw [ctot_cons, Ck.wt, ← add_assoc]; rw [hQ] at h2; linarith

end BB25
