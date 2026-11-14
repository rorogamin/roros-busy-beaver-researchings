import Accel.Exhaust

/-!
# The drain: base-3 counter + token word

The cells immediately to the left of the head hold a base-3 counter (least
significant digit nearest the head, digit symbols `3 = 0`, `4 = 1`, `0 = 2`),
terminated on the left by a frontier `1`.  To the right of the head is a token
word `w`.  Every complete return of `w` arrives at the least significant digit in
state `B`, performs one counter increment (possibly with overflow, which needs
blank tape left of the frontier), and re-enters `w` in state `A`.

`drain` combines this with the exhaustion normal form `exh_spec`: the machine
performs exactly `C` returns, the counter goes from `N` to `N + C`, the word is
replaced by `H`, and the head leaves to the right of the word, all in an exactly
known number of steps.
-/

namespace TM2x5

/-- The `m`-digit base-3 counter word holding `N` (least significant digit first). -/
def enc : ℕ → ℕ → List Sym
  | 0, _ => []
  | m + 1, N => dsym (N % 3) :: enc m (N / 3)

/-- The digit sum of the `m` lowest base-3 digits of `N`. -/
def dsum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, N => N % 3 + dsum m (N / 3)

/-- The cost of one non-overflowing increment of the `m`-digit counter `N`. -/
def incC : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, N => if N % 3 = 2 then incC m (N / 3) + 2 else 1

theorem dsym_zero : dsym 0 = 3 := rfl
theorem dsym_one : dsym 1 = 4 := rfl
theorem dsym_two : dsym 2 = 0 := rfl

theorem dsum_of_lt : ∀ (m N m' : ℕ), N < 3 ^ m → m ≤ m' → dsum m' N = dsum m N := by
  intro m
  induction m with
  | zero =>
    intro N m' hN _
    have : N = 0 := by simpa using hN
    subst this
    clear hN
    induction m' with
    | zero => rfl
    | succ k ih => simp [dsum, ih (Nat.zero_le _)]
  | succ m ih =>
    intro N m' hN hm
    obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
    simp only [dsum]
    rw [ih (N / 3) k (by rw [pow_succ] at hN; omega) (by omega)]

/-- One increment of a counter that does not overflow. -/
theorem inc_phys : ∀ (m N : ℕ), N + 1 < 3 ^ (m + 1) → ∀ (l xs : List Sym),
    iter (incC (m + 1) N) (some ⟨St.B, enc m (N / 3) ++ l, dsym (N % 3), xs⟩) =
      some (onFirst St.A (enc (m + 1) (N + 1) ++ l) xs) := by
  intro m
  induction m with
  | zero =>
    intro N hN l xs
    have h3 : N % 3 = 0 ∨ N % 3 = 1 := by simp at hN; omega
    rcases h3 with h | h
    · have e1 : (N + 1) % 3 = 1 := by omega
      simp only [incC, h, enc, e1]
      simpa [dsym] using step_B_three' l xs
    · have e1 : (N + 1) % 3 = 2 := by omega
      simp only [incC, h, enc, e1]
      simpa [dsym] using step_B_four' l xs
  | succ m ih =>
    intro N hN l xs
    have h3 : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have e1 : (N + 1) % 3 = 1 := by omega
      have e2 : (N + 1) / 3 = N / 3 := by omega
      simp only [incC, h, enc, e1, e2]
      simpa [dsym] using step_B_three' (enc (m + 1) (N / 3) ++ l) xs
    · have e1 : (N + 1) % 3 = 2 := by omega
      have e2 : (N + 1) / 3 = N / 3 := by omega
      simp only [incC, h, enc, e1, e2]
      simpa [dsym] using step_B_four' (enc (m + 1) (N / 3) ++ l) xs
    · have e1 : (N + 1) % 3 = 0 := by omega
      have e2 : (N + 1) / 3 = N / 3 + 1 := by omega
      have hN' : N / 3 + 1 < 3 ^ (m + 1) := by
        rw [pow_succ] at hN; omega
      have hc : incC (m + 1 + 1) N = 1 + (incC (m + 1) (N / 3) + 1) := by
        simp [incC, h]; omega
      rw [hc, iter_add]
      have h1 : iter 1 (some (⟨St.B, enc (m + 1) (N / 3) ++ l, dsym (N % 3), xs⟩ : Cfg)) =
          some ⟨St.B, enc m (N / 3 / 3) ++ l, dsym (N / 3 % 3), (2 : Sym) :: xs⟩ := by
        rw [h]; rfl
      rw [h1, iter_add, ih (N / 3) hN' l ((2 : Sym) :: xs)]
      simp only [onFirst_cons]
      rw [show (⟨St.A, enc (m + 1) (N / 3 + 1) ++ l, 2, xs⟩ : Cfg) =
          onFirst St.A (enc (m + 1) (N / 3 + 1) ++ l) ((2 : Sym) :: xs) from rfl,
        step_A_two']
      simp [enc, e1, e2, dsym]

theorem inc_cost : ∀ (m N : ℕ), N + 1 < 3 ^ (m + 1) →
    incC (m + 1) N + dsum (m + 1) (N + 1) = 2 + dsum (m + 1) N := by
  intro m
  induction m with
  | zero =>
    intro N hN
    have h3 : N % 3 = 0 ∨ N % 3 = 1 := by simp at hN; omega
    rcases h3 with h | h <;>
    · simp only [incC, dsum, h]
      have : (N + 1) % 3 = N % 3 + 1 := by omega
      simp [this, h]
  | succ m ih =>
    intro N hN
    have h3 : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have e1 : (N + 1) % 3 = 1 := by omega
      have e2 : (N + 1) / 3 = N / 3 := by omega
      have a1 : incC (m + 1 + 1) N = if N % 3 = 2 then incC (m + 1) (N / 3) + 2 else 1 := rfl
      have a2 : dsum (m + 1 + 1) (N + 1) = (N + 1) % 3 + dsum (m + 1) ((N + 1) / 3) := rfl
      have a3 : dsum (m + 1 + 1) N = N % 3 + dsum (m + 1) (N / 3) := rfl
      rw [a1, a2, a3, e1, e2, h]; simp; omega
    · have e1 : (N + 1) % 3 = 2 := by omega
      have e2 : (N + 1) / 3 = N / 3 := by omega
      have a1 : incC (m + 1 + 1) N = if N % 3 = 2 then incC (m + 1) (N / 3) + 2 else 1 := rfl
      have a2 : dsum (m + 1 + 1) (N + 1) = (N + 1) % 3 + dsum (m + 1) ((N + 1) / 3) := rfl
      have a3 : dsum (m + 1 + 1) N = N % 3 + dsum (m + 1) (N / 3) := rfl
      rw [a1, a2, a3, e1, e2, h]; simp; omega
    · have e1 : (N + 1) % 3 = 0 := by omega
      have e2 : (N + 1) / 3 = N / 3 + 1 := by omega
      have hN' : N / 3 + 1 < 3 ^ (m + 1) := by
        rw [pow_succ] at hN; omega
      have := ih (N / 3) hN'
      have a1 : incC (m + 1 + 1) N = if N % 3 = 2 then incC (m + 1) (N / 3) + 2 else 1 := rfl
      have a2 : dsum (m + 1 + 1) (N + 1) = (N + 1) % 3 + dsum (m + 1) ((N + 1) / 3) := rfl
      have a3 : dsum (m + 1 + 1) N = N % 3 + dsum (m + 1) (N / 3) := rfl
      rw [a1, a2, a3, e1, e2, h, if_pos rfl]
      omega

/-! ## Overflow -/

theorem enc_sat : ∀ m : ℕ, enc m (3 ^ m - 1) = List.replicate m (0 : Sym) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have e1 : (3 ^ (m + 1) - 1) % 3 = 2 := by rw [pow_succ]; omega
    have e2 : (3 ^ (m + 1) - 1) / 3 = 3 ^ m - 1 := by rw [pow_succ]; omega
    simp [enc, e1, e2, ih, List.replicate_succ, dsym]

theorem dsum_sat : ∀ m : ℕ, dsum m (3 ^ m - 1) = 2 * m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have e1 : (3 ^ (m + 1) - 1) % 3 = 2 := by rw [pow_succ]; omega
    have e2 : (3 ^ (m + 1) - 1) / 3 = 3 ^ m - 1 := by rw [pow_succ]; omega
    simp only [dsum, e1, e2, ih]; ring

theorem enc_pow : ∀ m : ℕ, enc (m + 1) (3 ^ m) = List.replicate m (3 : Sym) ++ [(4 : Sym)] := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have e1 : 3 ^ (m + 1) % 3 = 0 := by rw [pow_succ]; omega
    have e2 : 3 ^ (m + 1) / 3 = 3 ^ m := by rw [pow_succ]; omega
    rw [enc, e1, e2, ih]
    simp [List.replicate_succ, dsym]

theorem dsum_pow : ∀ m : ℕ, dsum (m + 1) (3 ^ m) = 1 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have e1 : 3 ^ (m + 1) % 3 = 0 := by rw [pow_succ]; omega
    have e2 : 3 ^ (m + 1) / 3 = 3 ^ m := by rw [pow_succ]; omega
    rw [dsum, e1, e2, ih]

theorem A_over_twos' : ∀ (k : ℕ) (l xs : List Sym),
    iter (k + 1) (some ⟨St.A, l, 2, List.replicate k (2 : Sym) ++ xs⟩) =
      some (onFirst St.A (List.replicate (k + 1) (3 : Sym) ++ l) xs) := by
  intro k
  induction k with
  | zero => intro l xs; exact step_A_two' l xs
  | succ k ih =>
    intro l xs
    rw [show k + 1 + 1 = 1 + (k + 1) by omega, iter_add]
    have h1 : iter 1 (some (⟨St.A, l, 2, List.replicate (k + 1) (2 : Sym) ++ xs⟩ : Cfg)) =
        some ⟨St.A, (3 : Sym) :: l, 2, List.replicate k (2 : Sym) ++ xs⟩ := by
      rw [List.replicate_succ]; rfl
    rw [h1, ih, show 1 + (k + 1) = k + 2 by omega]
    simp [List.replicate_succ', List.append_assoc]

theorem overflow_phys (k : ℕ) (xs : List Sym) :
    iter (2 * k + 5) (some ⟨St.B, List.replicate k (0 : Sym) ++ [1], 0, xs⟩) =
      some (onFirst St.A (List.replicate (k + 1) (3 : Sym) ++ [(4 : Sym), (1 : Sym)]) xs) := by
  rw [show 2 * k + 5 = (k + 2) + (2 + (k + 1)) by omega, iter_add,
    frontier_overflow_blank k xs, iter_add]
  have h2 : iter 2 (some (⟨St.A, [], 0,
      (3 : Sym) :: List.replicate (k + 1) (2 : Sym) ++ xs⟩ : Cfg)) =
      some ⟨St.A, [(4 : Sym), (1 : Sym)], 2, List.replicate k (2 : Sym) ++ xs⟩ := by
    rw [List.replicate_succ]; rfl
  rw [h2, A_over_twos']

/-! ## A batch of returns driven by the counter -/

theorem pow_lt_pow_of_lt' {a b : ℕ} (h : a < b) : 3 ^ a < 3 ^ b :=
  Nat.pow_lt_pow_right (by norm_num) h

/-- **Counter-driven batch.**  `k` returns of the word `u`, each followed by an
increment of the counter, take the counter from `N` (width `m`) to `N + k`
(width `m'`), with an explicitly known number of steps.  The width can only grow
if the tape left of the frontier is blank. -/
theorem phys_batch {k : ℕ} {u v : List Sym} {t : ℕ} (hb : ReturnBatch k u v t) :
    ∀ (m N : ℕ) (L r : List Sym) (m' : ℕ), 1 ≤ m → N < 3 ^ m → m ≤ m' → N + k < 3 ^ m' →
      (m < m' → 3 ^ (m' - 1) ≤ N + k) → (m < m' → L = []) →
      ∃ T, iter (t + T) (some (onFirst St.A (enc m N ++ (1 : Sym) :: L) (u ++ r))) =
          some (onFirst St.A (enc m' (N + k) ++ (1 : Sym) :: L) (v ++ r)) ∧
        T + dsum m' (N + k) = 2 * k + dsum m' N + 2 * (m' - m) := by
  induction hb with
  | nil u =>
    intro m N L r m' hm hN hmm hk hpow hL
    have hmm' : m' = m := by
      by_contra hne
      have hlt : m < m' := by omega
      have h1 := hpow hlt
      have h2 : 3 ^ m ≤ 3 ^ (m' - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hmm'
    exact ⟨0, rfl, by simp⟩
  | @cons k u u1 w n tb hr hbt ih =>
    intro m N L r m' hm hN hmm hk hpow hL
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    have hret := hr (dsym (N % 3)) (enc m0 (N / 3) ++ (1 : Sym) :: L) r
    have hstart : onFirst St.A (enc (m0 + 1) N ++ (1 : Sym) :: L) (u ++ r) =
        onFirst St.A (dsym (N % 3) :: (enc m0 (N / 3) ++ (1 : Sym) :: L)) (u ++ r) := rfl
    by_cases hov : N + 1 < 3 ^ (m0 + 1)
    · -- ordinary increment
      obtain ⟨T', hT', hcost⟩ := ih (m0 + 1) (N + 1) L r m' hm hov hmm (by omega)
        (fun h => by have := hpow h; omega) hL
      have hinc := inc_phys m0 N hov (1 :: L) (u1 ++ r)
      have hc := inc_cost m0 N hov
      have hw1 := dsum_of_lt (m0 + 1) N m' hN hmm
      have hw2 := dsum_of_lt (m0 + 1) (N + 1) m' hov hmm
      refine ⟨incC (m0 + 1) N + T', ?_, ?_⟩
      · rw [show n + tb + (incC (m0 + 1) N + T') = n + (incC (m0 + 1) N + (tb + T')) by omega,
          iter_add, hstart, hret, iter_add, hinc, hT', show N + 1 + k = N + (k + 1) by omega]
      · rw [show N + 1 + k = N + (k + 1) by omega] at hcost
        omega
    · -- overflow: the counter is saturated
      have hNeq : N = 3 ^ (m0 + 1) - 1 := by omega
      have hlt : m0 + 1 < m' := by
        by_contra hge
        have : 3 ^ m' ≤ 3 ^ (m0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hLnil := hL hlt
      subst hLnil
      have h1 : 1 ≤ 3 ^ (m0 + 1) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨T', hT', hcost⟩ := ih (m0 + 1 + 1) (N + 1) [] r m' (by omega)
        (by rw [pow_succ]; omega) (by omega) (by omega)
        (fun _ => by have := hpow hlt; omega) (fun _ => rfl)
      have hsat : enc (m0 + 1) N = List.replicate (m0 + 1) (0 : Sym) := by
        rw [hNeq]; exact enc_sat _
      have hovf := overflow_phys m0 (u1 ++ r)
      have hds1 : dsum m' N = 2 * (m0 + 1) := by
        rw [dsum_of_lt (m0 + 1) N m' hN hmm, hNeq, dsum_sat]
      have hds2 : dsum m' (N + 1) = 1 := by
        rw [dsum_of_lt (m0 + 1 + 1) (N + 1) m' (by rw [pow_succ]; omega) (by omega),
          show N + 1 = 3 ^ (m0 + 1) by omega, dsum_pow]
      refine ⟨2 * m0 + 5 + T', ?_, ?_⟩
      · rw [show n + tb + (2 * m0 + 5 + T') = n + (2 * m0 + 5 + (tb + T')) by omega,
          iter_add, hstart, hret, iter_add]
        have e3 : dsym (N % 3) = 0 := by
          have : N % 3 = 2 := by
            rw [hNeq]; rw [pow_succ]; omega
          rw [this]; rfl
        have e4 : enc m0 (N / 3) = List.replicate m0 (0 : Sym) := by
          have := hsat
          simp only [enc, List.replicate_succ, List.cons.injEq] at this
          exact this.2
        rw [e3, e4, hovf]
        have e5 : enc (m0 + 1 + 1) (N + 1) = List.replicate (m0 + 1) (3 : Sym) ++ [(4 : Sym)] := by
          rw [show N + 1 = 3 ^ (m0 + 1) by omega, enc_pow]
        rw [show N + 1 + k = N + (k + 1) by omega] at hT'
        rw [← hT', e5]
        simp
      · rw [show N + 1 + k = N + (k + 1) by omega] at hcost
        omega

/-! ## The drain -/

/-- **The drain.**  A counter `N` of width `m ≥ 1` (frontier `1`, then `L`) to the
left of the head, the token word `w` under and to the right of the head, state
`A`.  With `exh w = (C, H, T₀)`, after `T₀ + T` steps the counter holds `N + C`
in width `m'`, the word has become `H`, and the head is on the first cell after
the word in state `A`; `T` is given by the digit-sum formula. -/
theorem drain (w : List Tok) (m N : ℕ) (L r : List Sym) (m' : ℕ) (hm : 1 ≤ m)
    (hN : N < 3 ^ m) (hmm : m ≤ m') (hk : N + (exh w).1 < 3 ^ m')
    (hpow : m < m' → 3 ^ (m' - 1) ≤ N + (exh w).1) (hL : m < m' → L = []) :
    ∃ T, iter ((exh w).2.2 + T)
        (some (onFirst St.A (enc m N ++ (1 : Sym) :: L) (decode w ++ r))) =
        some (onFirst St.A ((exh w).2.1.reverse ++ enc m' (N + (exh w).1) ++ (1 : Sym) :: L) r) ∧
      T + dsum m' (N + (exh w).1) = 2 * (exh w).1 + dsum m' N + 2 * (m' - m) := by
  obtain ⟨v, t1, t2, hb, he, ht⟩ := exh_spec w
  obtain ⟨T, hT, hc⟩ := phys_batch hb m N L r m' hm hN hmm hk hpow hL
  refine ⟨T, ?_, hc⟩
  rw [ht, show t1 + t2 + T = (t1 + T) + t2 by omega, iter_add, hT, he]
  simp

end TM2x5
