import RequestProject.Tokens

/-!
# The carry, and how the machine performs it

`carry d w` is the counter word after a carry with `d` blocks of material
enters it at its right end (`none` if it runs off the left end); `cap w` is the
number of carries the word still admits.  `crossCarry` is the machine law: the
head crosses the word performing exactly this carry.
-/

namespace BB25

/-- **The cascade carry rule.**  `carry d w` is the word `w` (in reverse tape
order) after a carry entering at its right end with `d` blocks of material,
or `none` if the carry runs off the left end. -/
def carry : ℕ → List Tok → Option (List Tok)
  | _, [] => none
  | d, .P :: w => (carry (d + 1) w).map (Tok.P :: ·)
  | d + 1, .C :: w => (carry d w).map (Tok.C :: ·)
  | d + 1, .F :: w => (carry d w).map (Tok.F :: ·)
  | 0, .C :: w => (carry 0 w).map (Tok.F :: ·)
  | 0, .F :: w => some (Tok.C :: w)

@[simp] theorem carry_nil (d : ℕ) : carry d [] = none := by cases d <;> rfl

@[simp] theorem carry_P (d : ℕ) (w : List Tok) :
    carry d (.P :: w) = (carry (d + 1) w).map (Tok.P :: ·) := by cases d <;> rfl

@[simp] theorem carry_C_succ (d : ℕ) (w : List Tok) :
    carry (d + 1) (.C :: w) = (carry d w).map (Tok.C :: ·) := rfl

@[simp] theorem carry_F_succ (d : ℕ) (w : List Tok) :
    carry (d + 1) (.F :: w) = (carry d w).map (Tok.F :: ·) := rfl

@[simp] theorem carry_C_zero (w : List Tok) :
    carry 0 (.C :: w) = (carry 0 w).map (Tok.F :: ·) := rfl

@[simp] theorem carry_F_zero (w : List Tok) : carry 0 (.F :: w) = some (Tok.C :: w) := rfl

/-- The carry does not change the length of the word. -/
theorem carry_length : ∀ (d : ℕ) (w w' : List Tok), carry d w = some w' →
    w'.length = w.length := by
  intro d w
  induction w generalizing d with
  | nil => simp
  | cons x w ih =>
      intro w' h
      match x, d with
      | .P, d =>
          simp only [carry_P, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih (d + 1) v hv]
      | .C, d + 1 =>
          simp only [carry_C_succ, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih d v hv]
      | .F, d + 1 =>
          simp only [carry_F_succ, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih d v hv]
      | .C, 0 =>
          simp only [carry_C_zero, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih 0 v hv]
      | .F, 0 =>
          simp only [carry_F_zero, Option.some.injEq] at h
          simp [← h]

theorem carry_ne_nil {d : ℕ} {w w' : List Tok} (h : carry d w = some w') : w' ≠ [] := by
  intro hnil
  have hl := carry_length d w w' h
  rw [hnil] at hl
  cases w with
  | nil => simp at h
  | cons x w => simp at hl

/-- **Adding `2^{d+1}` is adding `2^d` twice.**  The identity that drives the
whole cascade. -/
theorem carry_double : ∀ (w : List Tok) (d : ℕ),
    carry (d + 1) w = (carry d w).bind (carry d) := by
  intro w
  induction w with
  | nil => simp
  | cons x w ih =>
      intro d
      match x, d with
      | .P, d =>
          simp only [carry_P, ih (d + 1), Option.map_bind, Option.bind_map]
          cases carry (d + 1) w with
          | none => rfl
          | some v => simp [carry_P]
      | .C, 0 =>
          simp only [carry_C_succ, carry_C_zero, Option.bind_map]
          cases carry 0 w with
          | none => rfl
          | some v => simp [carry_F_zero]
      | .C, d + 1 =>
          simp only [carry_C_succ, Option.bind_map, ih d]
          cases carry d w with
          | none => rfl
          | some v => simp [carry_C_succ]
      | .F, 0 => rfl
      | .F, d + 1 =>
          simp only [carry_F_succ, Option.bind_map, ih d]
          cases carry d w with
          | none => rfl
          | some v => simp [carry_F_succ]

/-- `2^{2d}`: the material of `d` blocks, as cells. -/
def mat (d : ℕ) : List Sym := List.replicate (2 * d) 2

/-- `P^d`: `d` blocks, as tokens. -/
def blocks (d : ℕ) : List Tok := List.replicate d .P

@[simp] theorem mat_zero : mat 0 = [] := rfl

@[simp] theorem blocks_zero : blocks 0 = [] := rfl

theorem mat_succ (d : ℕ) (r : List Sym) : mat (d + 1) ++ r = mat d ++ 2 :: 2 :: r := by
  simp only [mat, show 2 * (d + 1) = 2 * d + 2 by ring, List.replicate_add]
  simp

theorem blocks_succ (d : ℕ) : blocks (d + 1) = .P :: blocks d := rfl

/-- Dissolving `d` blocks at the right end of the word: the head pops them one
by one, turning each into two cells `2 2`. -/
theorem pop_blocks : ∀ (d : ℕ) (w : List Tok), w ≠ [] → ∀ s : List Sym,
    Reaches ⟨.L, blocks d ++ w, s⟩ ⟨.L, w, mat d ++ s⟩ := by
  intro d
  induction d with
  | zero => intro w _ s; simpa using Reaches.refl _
  | succ d ih =>
      intro w hw s
      obtain ⟨x, v, hxv⟩ : ∃ x v, blocks d ++ w = x :: v := by
        cases hbw : blocks d ++ w with
        | nil => exact absurd hbw (by simp [hw])
        | cons x v => exact ⟨x, v, rfl⟩
      have h1 : Reaches ⟨.L, blocks (d + 1) ++ w, s⟩ ⟨.L, blocks d ++ w, 2 :: 2 :: s⟩ := by
        rw [blocks_succ, List.cons_append, hxv]
        exact Reaches.step (c := ⟨.L, .P :: x :: v, s⟩) rfl
      have h2 := (h1.trans (ih w hw (2 :: 2 :: s)))
      rwa [show mat d ++ 2 :: 2 :: s = mat (d + 1) ++ s from (mat_succ d s).symm] at h2

/-! ## The crossing law for an arbitrary word -/

/-- **The cascade crossing law.**  If `carry d W = some W'` then the head,
arriving at the right end of `W` with `d` blocks' worth of material and an
arbitrary word `r` beyond it, comes back out moving right in front of `r`,
having turned the material into `d` new blocks and the word into `W'`. -/
theorem crossCarry : ∀ (n d : ℕ) (W W' : List Tok), W.length ≤ n → carry d W = some W' →
    ∀ r : List Sym, Reaches ⟨.L, W, mat d ++ r⟩ ⟨.R, blocks d ++ W', r⟩ := by
  intro n
  induction n with
  | zero =>
      intro d W W' hW hc
      have : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hW)
      subst this
      simp at hc
  | succ n ih =>
      intro d
      induction d with
      | zero =>
          intro W W' hW hc r
          match W with
          | [] => simp at hc
          | .F :: w =>
              simp only [carry_F_zero, Option.some.injEq] at hc
              subst hc
              simpa using Reaches.step (c := ⟨.L, .F :: w, r⟩) rfl
          | .P :: w =>
              simp only [carry_P, Option.map_eq_some_iff] at hc
              obtain ⟨W₁, hW₁, rfl⟩ := hc
              obtain ⟨x, v, rfl⟩ : ∃ x v, w = x :: v := by
                cases w with
                | nil => simp at hW₁
                | cons x v => exact ⟨x, v, rfl⟩
              have h1 : Reaches ⟨.L, .P :: x :: v, r⟩ ⟨.L, x :: v, 2 :: 2 :: r⟩ :=
                Reaches.step (c := ⟨.L, .P :: x :: v, r⟩) rfl
              have h2 := ih 1 (x :: v) W₁ (by simp at hW ⊢; omega) hW₁ r
              rw [show mat 1 ++ r = 2 :: 2 :: r by simp [mat]] at h2
              simpa [blocks_succ] using (h1.trans h2)
          | .C :: w =>
              simp only [carry_C_zero, Option.map_eq_some_iff] at hc
              obtain ⟨W₁, hW₁, rfl⟩ := hc
              match w with
              | [] => simp at hW₁
              | .F :: y =>
                  simp only [carry_F_zero, Option.some.injEq] at hW₁
                  subst hW₁
                  have h1 : Reaches ⟨.L, .C :: .F :: y, r⟩ ⟨.R, .C :: y, 3 :: 3 :: r⟩ :=
                    Reaches.step (c := ⟨.L, .C :: .F :: y, r⟩) rfl
                  have h2 : Reaches ⟨.R, .C :: y, 3 :: 3 :: r⟩ ⟨.R, .F :: .C :: y, r⟩ :=
                    Reaches.step (c := ⟨.R, .C :: y, 3 :: 3 :: r⟩) rfl
                  simpa using h1.trans h2
              | .C :: v =>
                  simp only [carry_C_zero, Option.map_eq_some_iff] at hW₁
                  obtain ⟨W₂, hW₂, rfl⟩ := hW₁
                  obtain ⟨x, v', rfl⟩ : ∃ x v', v = x :: v' := by
                    cases v with
                    | nil => simp at hW₂
                    | cons x v' => exact ⟨x, v', rfl⟩
                  have h1 : Reaches ⟨.L, .C :: .C :: x :: v', r⟩
                      ⟨.L, x :: v', 3 :: 3 :: 3 :: 3 :: r⟩ :=
                    Reaches.step (c := ⟨.L, .C :: .C :: x :: v', r⟩) rfl
                  have h2 := ih 0 (x :: v') W₂ (by simp at hW ⊢; omega) hW₂
                    (3 :: 3 :: 3 :: 3 :: r)
                  simp only [mat_zero, List.nil_append, blocks_zero] at h2
                  have h3 : Reaches ⟨.R, W₂, 3 :: 3 :: 3 :: 3 :: r⟩ ⟨.R, .F :: W₂, 3 :: 3 :: r⟩ :=
                    Reaches.step (c := ⟨.R, W₂, 3 :: 3 :: 3 :: 3 :: r⟩) rfl
                  have h4 : Reaches ⟨.R, .F :: W₂, 3 :: 3 :: r⟩ ⟨.R, .F :: .F :: W₂, r⟩ :=
                    Reaches.step (c := ⟨.R, .F :: W₂, 3 :: 3 :: r⟩) rfl
                  simpa using ((h1.trans h2).trans h3).trans h4
              | .P :: v =>
                  simp only [carry_P, Option.map_eq_some_iff] at hW₁
                  obtain ⟨W₂, hW₂, rfl⟩ := hW₁
                  obtain ⟨x, v', rfl⟩ : ∃ x v', v = x :: v' := by
                    cases v with
                    | nil => simp at hW₂
                    | cons x v' => exact ⟨x, v', rfl⟩
                  have h1 : Reaches ⟨.L, .C :: .P :: x :: v', r⟩
                      ⟨.L, x :: v', 2 :: 2 :: 3 :: 3 :: r⟩ :=
                    Reaches.step (c := ⟨.L, .C :: .P :: x :: v', r⟩) rfl
                  have h2 := ih 1 (x :: v') W₂ (by simp at hW ⊢; omega) hW₂ (3 :: 3 :: r)
                  rw [show mat 1 ++ (3 :: 3 :: r) = 2 :: 2 :: 3 :: 3 :: r by simp [mat]] at h2
                  have h3 : Reaches ⟨.R, blocks 1 ++ W₂, 3 :: 3 :: r⟩
                      ⟨.R, .F :: (blocks 1 ++ W₂), r⟩ :=
                    Reaches.step (c := ⟨.R, blocks 1 ++ W₂, 3 :: 3 :: r⟩) rfl
                  simpa [blocks_succ] using (h1.trans h2).trans h3
      | succ e ihd =>
          intro W W' hW hc r
          rw [carry_double, Option.bind_eq_some_iff] at hc
          obtain ⟨W₁, hc₁, hc₂⟩ := hc
          have hW₁ : W₁ ≠ [] := carry_ne_nil hc₁
          have hlen₁ : W₁.length ≤ n + 1 := by
            rw [carry_length e W W₁ hc₁]; exact hW
          -- first crossing
          have h1 := ihd W W₁ hW hc₁ (2 :: 2 :: r)
          rw [← mat_succ] at h1
          -- the head turns around on the first `2`
          obtain ⟨x, v, hxv⟩ : ∃ x v, blocks e ++ W₁ = x :: v := by
            cases hbw : blocks e ++ W₁ with
            | nil => exact absurd hbw (by simp [hW₁])
            | cons x v => exact ⟨x, v, rfl⟩
          have h2 : Reaches ⟨.R, blocks e ++ W₁, 2 :: 2 :: r⟩ ⟨.L, blocks e ++ W₁, 3 :: 2 :: r⟩ := by
            rw [hxv]
            exact Reaches.step (c := ⟨.R, x :: v, 2 :: 2 :: r⟩) rfl
          -- and dissolves the blocks it has just made
          have h3 := pop_blocks e W₁ hW₁ (3 :: 2 :: r)
          -- second crossing
          have h4 := ihd W₁ W' hlen₁ hc₂ (3 :: 2 :: r)
          -- the `3 2` left over becomes the last block
          have h5 : Reaches ⟨.R, blocks e ++ W', 3 :: 2 :: r⟩ ⟨.R, .P :: (blocks e ++ W'), r⟩ :=
            Reaches.step (c := ⟨.R, blocks e ++ W', 3 :: 2 :: r⟩) rfl
          have := (((h1.trans h2).trans h3).trans h4).trans h5
          simpa [blocks_succ] using this

/-- **The pass law.**  If the carry does not run off the left end, one pass
over `X` replaces `X` by `carry 0 X` and appends one block. -/
theorem cascade_pass_tok (X X' : List Tok) (h : carry 0 X = some X') :
    Reaches ⟨.L, X, [3, 2]⟩ ⟨.L, .P :: X', [3, 2]⟩ := by
  have h1 := crossCarry X.length 0 X X' (le_refl _) h [3, 2]
  simp only [mat_zero, List.nil_append, blocks_zero] at h1
  have h2 : Reaches ⟨.R, X', [3, 2]⟩ ⟨.R, .P :: X', []⟩ :=
    Reaches.step (c := ⟨.R, X', ([3, 2] : List Sym)⟩) rfl
  have h3 : Reaches ⟨.R, .P :: X', ([] : List Sym)⟩ ⟨.L, .P :: X', [3, 2]⟩ :=
    Reaches.step (c := ⟨.R, .P :: X', ([] : List Sym)⟩) rfl
  exact ((h1.trans h2).trans h3)

/-! ## The capacity -/

/-- **The capacity of a word**: the number of carries it still admits before a
carry runs off its left end. -/
def cap : List Tok → ℕ
  | [] => 0
  | .F :: w => 2 * cap w + 1
  | .C :: w => 2 * cap w
  | .P :: w => cap w / 2

@[simp] theorem cap_nil : cap [] = 0 := rfl
@[simp] theorem cap_F (w : List Tok) : cap (.F :: w) = 2 * cap w + 1 := rfl
@[simp] theorem cap_C (w : List Tok) : cap (.C :: w) = 2 * cap w := rfl
@[simp] theorem cap_P (w : List Tok) : cap (.P :: w) = cap w / 2 := rfl

/-- **A carry overflows exactly when the capacity is too small.** -/
theorem cap_carry_iff : ∀ (w : List Tok) (d : ℕ), carry d w = none ↔ cap w < 2 ^ d := by
  intro w
  induction w with
  | nil => intro d; simp
  | cons x w ih =>
      intro d
      match x, d with
      | .F, 0 => simp
      | .F, e + 1 =>
          rw [carry_F_succ, Option.map_eq_none_iff, ih e, cap_F, pow_succ]
          omega
      | .C, 0 =>
          rw [carry_C_zero, Option.map_eq_none_iff, ih 0, cap_C, pow_zero]
          omega
      | .C, e + 1 =>
          rw [carry_C_succ, Option.map_eq_none_iff, ih e, cap_C, pow_succ]
          omega
      | .P, d =>
          rw [carry_P, Option.map_eq_none_iff, ih (d + 1), cap_P, pow_succ]
          omega

/-- **A carry spends exactly `2 ^ d` of the capacity.** -/
theorem cap_carry : ∀ (w : List Tok) (d : ℕ) (w' : List Tok), carry d w = some w' →
    cap w' = cap w - 2 ^ d := by
  intro w
  induction w with
  | nil => intro d w' h; simp at h
  | cons x w ih =>
      intro d w' h
      match x, d with
      | .F, 0 =>
          rw [carry_F_zero, Option.some.injEq] at h
          subst h
          simp
      | .F, e + 1 =>
          rw [carry_F_succ, Option.map_eq_some_iff] at h
          obtain ⟨z, hz, rfl⟩ := h
          have hlt : 2 ^ e ≤ cap w := by
            by_contra hc
            exact (Option.some_ne_none z (by rw [← hz, (cap_carry_iff w e).2 (by omega)])).elim
          rw [cap_F, cap_F, ih e z hz, pow_succ]
          omega
      | .C, 0 =>
          rw [carry_C_zero, Option.map_eq_some_iff] at h
          obtain ⟨z, hz, rfl⟩ := h
          have hlt : 1 ≤ cap w := by
            by_contra hc
            exact (Option.some_ne_none z (by rw [← hz, (cap_carry_iff w 0).2 (by simpa using by omega)])).elim
          rw [cap_F, cap_C, ih 0 z hz, pow_zero]
          omega
      | .C, e + 1 =>
          rw [carry_C_succ, Option.map_eq_some_iff] at h
          obtain ⟨z, hz, rfl⟩ := h
          have hlt : 2 ^ e ≤ cap w := by
            by_contra hc
            exact (Option.some_ne_none z (by rw [← hz, (cap_carry_iff w e).2 (by omega)])).elim
          rw [cap_C, cap_C, ih e z hz, pow_succ]
          omega
      | .P, d =>
          rw [carry_P, Option.map_eq_some_iff] at h
          obtain ⟨z, hz, rfl⟩ := h
          have hlt : 2 ^ (d + 1) ≤ cap w := by
            by_contra hc
            exact (Option.some_ne_none z (by rw [← hz, (cap_carry_iff w (d + 1)).2 (by omega)])).elim
          rw [cap_P, cap_P, ih (d + 1) z hz, pow_succ]
          omega

/-- The capacity of a word behind a run of blocks. -/
theorem cap_replicate_P : ∀ (t : ℕ) (V : List Tok),
    cap (List.replicate t .P ++ V) = cap V / 2 ^ t
  | 0, V => by simp
  | t + 1, V => by
      rw [List.replicate_succ, List.cons_append, cap_P, cap_replicate_P t V,
        Nat.div_div_eq_div_mul, pow_succ]

/-- A carry entering a run of blocks comes out of it with `t` blocks' worth of
material. -/
theorem carry_replicate_P : ∀ (t : ℕ) (V : List Tok),
    carry 0 (List.replicate t .P ++ V)
      = (carry t V).map (fun V' => List.replicate t .P ++ V') := by
  have key : ∀ (t d : ℕ) (V : List Tok),
      carry d (List.replicate t .P ++ V)
        = (carry (d + t) V).map (fun V' => List.replicate t .P ++ V') := by
    intro t
    induction t with
    | zero => intro d V; simp
    | succ t ih =>
        intro d V
        rw [List.replicate_succ, List.cons_append, carry_P, ih (d + 1) V]
        rw [Option.map_map]
        have : d + 1 + t = d + (t + 1) := by omega
        rw [this]
        rfl
  intro t V
  simpa using key t 0 V

/-- At a `P` with capacity zero the tail has capacity at most one. -/
theorem cap_P_tail {w : List Tok} (h : cap (.P :: w) = 0) : cap w ≤ 1 := by
  rw [cap_P] at h
  omega

end BB25
