/-
# The word a drain deposits, and why its scan is safe

Sections 5–6 of the submitted argument.  A `<B1` sweep of `1LA` that reaches a
one bit ends — after the pending `2>` has pushed its run of `22` blocks, the
terminal `1` has turned the head around and the drain has emptied the counter —
at the paid stack of the reset word

```
  P(σ) Y^q V chi(2^(q-1) (cval σ + 1)) V ,
```

`σ` being the stack the sweep left behind (`Exact.lean` proves that this is
literally the checkpoint the machine reaches).  Since
`chi (2^(q-1) m) = X^(q-1) chi m`, this is the word of the document, the
`X^(q-1)` buffer included.

`ready_drain_word` is the readiness of that word, for every good `σ` and every
`q ≥ 2`.  The scan is read backwards: the last `V` costs nothing, `chi m` is
crossed by `ready_chi`, the buffer doubles `n+4` once per pop, the `V` in front
of it halves the debt, and the run `Y^q` then stops the scan unless `q = 2` and
the debt is `1 (mod 4)`.  In that one remaining case the inequality
`n + 9 ≤ 2m` carried out of `chi m` leaves a debt small enough for the
dual-credit lemma over `P(σ)`.
-/
import RequestProject.BB25.Prefix.LA.Chi

namespace BB25.Prefix

open BB25

/-- A run of one bits in front of an even debt stops the scan. -/
theorem ready_Yrun_even {pre : List RB} {q n : ℕ} (h : n % 2 = 0) :
    Ready (dpow n (TW (pre ++ List.replicate (q + 1) .Y))) := by
  have hcat : pre ++ List.replicate (q + 1) RB.Y
      = (pre ++ List.replicate q RB.Y) ++ [RB.Y] := by
    rw [List.replicate_succ']
    simp
  rw [hcat]
  exact ready_Y_even h

/-- **Every drain word is ready.** -/
theorem ready_drain_word {σ : List LB} (hg : Good σ) {q : ℕ} (hq : 2 ≤ q) :
    Ready (TW (pdec σ ++ List.replicate q RB.Y ++ [RB.V]
      ++ chi (2 ^ (q - 1) * (cval σ + 1)) ++ [RB.V])) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 2 := ⟨q - 2, by omega⟩
  set m : ℕ := cval σ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  -- the decoded value of the source stack
  set B : ℕ := cval (TW (pdec σ)) with hB
  have hBv : (B : ℤ) = bval σ := cval_TW_pdec hg
  have hBa : cval σ ≤ B := by
    have := hg.head
    omega
  have hstC : CStack (TW (pdec σ)) := CStack_TW_pdec hg
  -- the buffer is the head of the drain digits
  rw [show s + 2 - 1 = s + 1 from rfl, chi_two_pow (s + 1) m hm1]
  -- the four milestones of the word
  set w1 : List RB := pdec σ ++ List.replicate (s + 2) RB.Y with hw1
  set w2 : List RB := w1 ++ [RB.V] with hw2
  set w3 : List RB := w2 ++ List.replicate (s + 1) RB.X with hw3
  have hword : pdec σ ++ List.replicate (s + 2) RB.Y ++ [RB.V]
        ++ (List.replicate (s + 1) RB.X ++ chi m) ++ [RB.V]
      = (w3 ++ chi m) ++ [RB.V] := by
    rw [hw3, hw2, hw1]
    simp [List.append_assoc]
  rw [hword]
  have hstW1 : CStack (TW w1) := CStack_TW_Yrun hstC _
  have hstW2 : CStack (TW w2) := CStack_TW_V hstW1
  have hstW3 : CStack (TW w3) := CStack_TW_Xrun hstW2 _
  have hmb0 : m ≤ B + 1 := by omega
  -- the values along the word
  have hv1 : cval (TW w1) + 1 = 2 ^ (s + 2) * (B + 1) := cval_TW_Yrun _ _
  have hv2 : cval (TW w2) = 2 * cval (TW w1) := cval_TW_V _
  have hq2 : cval (TW w2) + 2 = 2 ^ (s + 1) * (4 * (B + 1)) := by
    have hpow : (2 : ℕ) ^ (s + 1) * (4 * (B + 1)) = 2 * (2 ^ (s + 2) * (B + 1)) := by
      ring
    omega
  have hv3 : cval (TW w3) + 2 = 4 * (B + 1) :=
    cval_TW_Xrun (s + 1) (4 * (B + 1)) w2 hstW2 (by omega) hq2
  -- the scan, read backwards
  refine ready_V_even (u := w3 ++ chi m) (n := 0) rfl ?_
  simp only [Nat.zero_div, dpow_zero]
  refine ready_chi m hm1 w3 hstW3 (by omega) ?_
  intro n hn hodd
  -- the buffer
  refine ready_Xrun (s + 1) n w2 hstW2 ?_ ?_
  · have h1 : 2 ^ (s + 1) * (n + 4) ≤ 2 ^ (s + 1) * (4 * m) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2' : (2:ℕ) ^ (s + 1) * (4 * m) ≤ 2 ^ (s + 1) * (4 * (B + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · -- the `V` in front of the buffer halves the debt
    have hpos : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hQ : (2:ℕ) ^ (s + 1) * (n + 4) = 2 * (2 ^ s * (n + 4)) := by rw [pow_succ]; ring
    have hbig : 4 ≤ 2 ^ s * (n + 4) := by nlinarith
    refine ready_V_even (u := w1) (by omega) ?_
    have hhalf : (2 ^ (s + 1) * (n + 4) - 4) / 2 = 2 ^ s * (n + 4) - 2 := by
      omega
    rw [hhalf]
    -- the run of one bits
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · -- `q = 2`: the two one bits may both be crossed
      simp only [pow_zero, one_mul]
      by_cases hnpar : n % 2 = 0
      · exact ready_Yrun_even (q := 1) (by omega)
      · -- the first one bit is crossed
        have hcat : pdec σ ++ List.replicate 2 RB.Y = (pdec σ ++ [RB.Y]) ++ [RB.Y] := by
          simp [List.replicate_succ]
        rw [hw1, hcat]
        refine ready_Y_odd (by omega) ?_
        rw [show (n + 4 - 2 - 1) / 2 = (n + 1) / 2 by omega]
        by_cases hnpar4 : n % 4 = 3
        · exact ready_Y_even (by omega)
        · -- the second one bit is crossed too: the dual-credit lemma finishes
          have hn4 : n % 4 = 1 := by omega
          refine ready_Y_odd (by omega) ?_
          rw [show ((n + 1) / 2 - 1) / 2 = (n - 1) / 4 by omega]
          have hnodd : n + 9 ≤ 2 * m := hodd (by omega)
          exact ready_dpow_of_cval hg (by omega)
    · -- `q ≥ 3`: the debt is even and the last one bit stops the scan
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have heven : (2 ^ (s' + 1) * (n + 4) - 2) % 2 = 0 := by
        have hQ' : (2:ℕ) ^ (s' + 1) * (n + 4) = 2 * (2 ^ s' * (n + 4)) := by rw [pow_succ]; ring
        have hpos' : 1 ≤ 2 ^ s' := Nat.one_le_two_pow
        have : 4 ≤ 2 ^ s' * (n + 4) := by nlinarith
        omega
      exact ready_Yrun_even (q := s' + 2) heven

end BB25.Prefix
