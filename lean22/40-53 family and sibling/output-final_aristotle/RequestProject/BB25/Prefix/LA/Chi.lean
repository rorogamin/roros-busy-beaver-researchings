/-
# The word a direct return of `1LA` deposits, and why its scan is safe

Section 5 of the submitted argument computes the reset word of a direct return
of the `01` branch:

```
  P(c) d Y^r V X^(r-1) chi(m) V,          m = ⌊cval c / 2⌋,
```

`d` being a zero bit for an even counter and a one bit for an odd one.  The
`X^(r-1)` block is the *buffer* left by the first `r-1` rounds of the drain and
`chi m` — the low binary digits of `m`, least significant first — is what the
remaining rounds emit.

This file proves that the paid stack of such a word is **ready**: its `1LA`
scan meets no pop it cannot pay for.  The scan is read backwards, as a debt
travelling right to left through the word (`Debt.lean`), and the three
ingredients are

* `ready_chi`: crossing `chi m` backwards, the debt `n` that arrives at the
  left of `chi m` always satisfies `n + 4 ≤ 4m`, and `n + 9 ≤ 2m` when it is
  odd — the two inequalities of Section 6;
* `ready_Xrun`: crossing the buffer backwards multiplies `n + 4` by `2^(r-1)`;
* `ready_Aword`: the assembly, where the two `V`s and the run `Y^r` either stop
  the scan outright or leave a debt small enough for the dual-credit lemma of
  `Debt.lean` to finish the job over `P(c)`.
-/
import RequestProject.BB25.Prefix.LA.Debt

namespace BB25.Prefix

open BB25

/-! ## Runs of letters -/

theorem CStack_TW_Yrun {pre : List RB} (h : CStack (TW pre)) (r : ℕ) :
    CStack (TW (pre ++ List.replicate r .Y)) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [List.replicate_succ', ← List.append_assoc]
      exact CStack_TW_Y ih

theorem CStack_TW_Xrun {pre : List RB} (h : CStack (TW pre)) (r : ℕ) :
    CStack (TW (pre ++ List.replicate r .X)) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [List.replicate_succ', ← List.append_assoc]
      exact CStack_TW_X ih

theorem cval_TW_Yrun (r : ℕ) (pre : List RB) :
    cval (TW (pre ++ List.replicate r .Y)) + 1 = 2 ^ r * (cval (TW pre) + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ', ← List.append_assoc, cval_TW_Y,
        show (2:ℕ) ^ (r + 1) * (cval (TW pre) + 1) = 2 * (2 ^ r * (cval (TW pre) + 1)) by ring,
        ← ih]
      omega

/-- The value of the buffer: `r-1` pops divide `value + 2` by `2^(r-1)`. -/
theorem cval_TW_Xrun : ∀ (k q : ℕ) (pre : List RB), CStack (TW pre) → 2 ≤ q →
    cval (TW pre) + 2 = 2 ^ k * q → cval (TW (pre ++ List.replicate k .X)) + 2 = q := by
  intro k
  induction k with
  | zero => intro q pre _ _ h; simpa using by simpa using h
  | succ k ih =>
      intro q pre hst hq h
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ≤ cval (TW pre) := by
        have : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by ring
        have h4 : 4 ≤ 2 ^ k * q * 2 := by nlinarith
        omega
      have hval : cval (TW (pre ++ [RB.X])) + 2 = 2 ^ k * q := by
        rw [cval_TW_X hst h2]
        have : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by ring
        omega
      have hcat : pre ++ List.replicate (k + 1) RB.X
          = (pre ++ [RB.X]) ++ List.replicate k RB.X := by
        simp [List.replicate_succ]
      rw [hcat]
      exact ih q (pre ++ [RB.X]) (CStack_TW_X hst) hq hval

/-- **Crossing the buffer backwards.**  Each pop doubles `n + 4`. -/
theorem ready_Xrun : ∀ (k n : ℕ) (pre : List RB), CStack (TW pre) →
    2 ^ k * (n + 4) ≤ cval (TW pre) + 4 →
    Ready (dpow (2 ^ k * (n + 4) - 4) (TW pre)) →
    Ready (dpow n (TW (pre ++ List.replicate k .X))) := by
  intro k
  induction k with
  | zero => intro n pre _ _ h; simpa using h
  | succ k ih =>
      intro n pre hst hle hrd
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hkey : 2 ^ (k + 1) * (n + 4) = 2 * (2 ^ k * (n + 4)) := by ring
      have hbig : 8 ≤ 2 ^ (k + 1) * (n + 4) := by nlinarith
      have h2 : 2 ≤ cval (TW pre) := by omega
      -- one pop of the buffer
      have hstep : Ready (dpow (2 ^ k * (n + 4) - 4) (TW (pre ++ [RB.X]))) := by
        refine ready_X hst ?_ ?_
        · omega
        · have he : 2 * (2 ^ k * (n + 4) - 4) + 4 = 2 ^ (k + 1) * (n + 4) - 4 := by omega
          rw [he]
          exact hrd
      have hval : cval (TW (pre ++ [RB.X])) = (cval (TW pre) - 2) / 2 := cval_TW_X hst h2
      have hcat : pre ++ List.replicate (k + 1) RB.X
          = (pre ++ [RB.X]) ++ List.replicate k RB.X := by
        simp [List.replicate_succ]
      rw [hcat]
      exact ih n (pre ++ [RB.X]) (CStack_TW_X hst) (by omega) hstep

/-! ## The digits of the drain -/

/-- The low binary digits of `m`, least significant first: a zero digit is the
pop `X`, a one digit the pop `V`.  The leading one of `m` is omitted. -/
def chi (m : ℕ) : List RB :=
  if 2 ≤ m then (if m % 2 = 0 then RB.X else RB.V) :: chi (m / 2) else []
termination_by m
decreasing_by omega

theorem chi_of_lt {m : ℕ} (h : m < 2) : chi m = [] := by
  rw [chi, if_neg (by omega)]

theorem chi_of_le {m : ℕ} (h : 2 ≤ m) :
    chi m = (if m % 2 = 0 then RB.X else RB.V) :: chi (m / 2) := by
  rw [chi, if_pos h]

/-- **Crossing `chi m` backwards.**  The scan enters the digits with no debt;
whatever debt it carries out at the left satisfies `n + 4 ≤ 4m`, and
`n + 9 ≤ 2m` if it is odd, which is all the continuation needs. -/
theorem ready_chi : ∀ (m : ℕ), 1 ≤ m → ∀ pre : List RB, CStack (TW pre) →
    4 * m ≤ cval (TW pre) + 2 →
    (∀ n : ℕ, n + 4 ≤ 4 * m → (n % 2 = 1 → n + 9 ≤ 2 * m) → Ready (dpow n (TW pre))) →
    Ready (TW (pre ++ chi m)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm pre hst hval hcont
      rcases lt_or_ge m 2 with hlt | hge
      · obtain rfl : m = 1 := by omega
        rw [chi_of_lt (by omega)]
        simpa using hcont 0 (by omega) (by omega)
      · set m' : ℕ := m / 2 with hm'
        have hm'1 : 1 ≤ m' := by omega
        have hm'lt : m' < m := by omega
        rw [chi_of_le hge]
        by_cases hpar : m % 2 = 0
        · -- an even digit: the letter is a pop matched to a zero bit
          rw [if_pos hpar]
          have hmm : m = 2 * m' := by omega
          have h2 : 2 ≤ cval (TW pre) := by omega
          have hvalX : cval (TW (pre ++ [RB.X])) = (cval (TW pre) - 2) / 2 :=
            cval_TW_X hst h2
          have hrun : Ready (TW ((pre ++ [RB.X]) ++ chi m')) := by
            refine ih m' hm'lt hm'1 (pre ++ [RB.X]) (CStack_TW_X hst) (by omega) ?_
            intro n hn _
            refine ready_X hst (by omega) ?_
            exact hcont (2 * n + 4) (by omega) (by omega)
          simpa using hrun
        · -- an odd digit: the letter is a pop matched to a one bit
          rw [if_neg hpar]
          have hmm : m = 2 * m' + 1 := by omega
          have hvalV : cval (TW (pre ++ [RB.V])) = 2 * cval (TW pre) := cval_TW_V pre
          have hrun : Ready (TW ((pre ++ [RB.V]) ++ chi m')) := by
            refine ih m' hm'lt hm'1 (pre ++ [RB.V]) (CStack_TW_V hst) (by omega) ?_
            intro n hn hodd
            by_cases hp : n % 2 = 1
            · exact ready_V_odd hp
            · refine ready_V_even (by omega) ?_
              refine hcont (n / 2) (by omega) ?_
              intro hq
              -- an odd halved debt forces `n ≡ 2 (mod 4)`, hence `m' ≥ 2`
              omega
          simpa using hrun

/-! ## Digits of a power of two -/

/-- The digits of `2^k m` start with `k` zero digits. -/
theorem chi_two_pow : ∀ (k M : ℕ), 1 ≤ M → chi (2 ^ k * M) = List.replicate k .X ++ chi M := by
  intro k
  induction k with
  | zero => intro M _; simp
  | succ k ih =>
      intro M hM
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ≤ 2 ^ (k + 1) * M := by
        have : (2:ℕ) ^ (k + 1) * M = 2 * (2 ^ k * M) := by ring
        nlinarith
      have hhalf : 2 ^ (k + 1) * M / 2 = 2 ^ k * M := by
        have : (2:ℕ) ^ (k + 1) * M = 2 * (2 ^ k * M) := by ring
        omega
      have heven : 2 ^ (k + 1) * M % 2 = 0 := by
        have : (2:ℕ) ^ (k + 1) * M = 2 * (2 ^ k * M) := by ring
        omega
      rw [chi_of_le h2, if_pos heven, hhalf, ih M hM, List.replicate_succ, List.cons_append]

end BB25.Prefix
