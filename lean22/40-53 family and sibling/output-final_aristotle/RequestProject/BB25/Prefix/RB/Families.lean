/-
# The scans of the six exceptional families

`Classify.lean` shows that a generated word either satisfies the leading-run
criterion of `Credit.lean` or belongs to one of four explicit shapes (six
families once the small parameters are spelled out).  This file runs the
reverse scan of each of those shapes by hand.

All of them end in the core `Y Y V` of a base word, followed by a run of pops
and zero bits, and the scan behaves the same way in every case: it crosses the
trailing pops, arrives at the `V` of the core with a debt divisible by four,
halves it once and stops at the `Y` in front of it, whose parity check the even
debt fails.  The two ingredients are therefore

* `scan_stop_YV` — a debt divisible by four stops at a `Y V`;
* `scan_Xrun` — a run of `c` pops multiplies the debt-plus-four by `2^c`, and
  the whole run is supplied as soon as the value in front of it is at least the
  exit debt (`rrun_credit` distributes that single inequality over the run).
-/
import RequestProject.BB25.Prefix.RB.Classify

namespace BB25.Prefix

open BB25

variable {a : ℤ} {Q : ℕ → Prop}

/-! ## The two generic scan steps -/

/-- A debt divisible by four stops the scan at a `Y V`. -/
theorem scan_stop_YV (u : List RB) {n : ℕ} (h : n % 4 = 0) :
    Scan (u ++ [.Y, .V]) n a Q := by
  rw [show u ++ [RB.Y, RB.V] = (u ++ [RB.Y]) ++ [RB.V] by simp]
  refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
  exact Scan_snoc_Y.mpr (Or.inl (by omega))

theorem digs_Xrun (c : ℕ) : Digs (List.replicate c .X) := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact Or.inr (Or.inr rfl)

/-- **A run of pops.**  Crossing `c` pops takes the debt `n` to the debt `m`
with `m + 4 = 2^c (n + 4)`, and the whole run is supplied as soon as the value
in front of it is at least `m + 2`. -/
theorem scan_Xrun {pre : List RB} : ∀ (c : ℕ) {n m : ℕ}, m + 4 = 2 ^ c * (n + 4) →
    ((m : ℤ) + 4 ≤ rrun pre a + 2) → Scan pre m a Q →
    Scan (pre ++ List.replicate c .X) n a Q := by
  intro c
  induction c with
  | zero =>
      intro n m hm hb hs
      simp only [pow_zero, one_mul] at hm
      simpa [show m = n by omega] using hs
  | succ c ih =>
      intro n m hm hb hs
      rw [List.replicate_succ', ← List.append_assoc]
      refine Scan_snoc_X.mpr ⟨?_, ih (n := 2 * n + 4) (m := m) (by rw [hm]; ring) hb hs⟩
      -- the supply of the rightmost pop
      set b := rrun pre a with hbdef
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      have hmz : ((m : ℤ) + 4) = 2 ^ (c + 1) * ((n : ℤ) + 4) := by exact_mod_cast hm
      have hbig : ((2 : ℤ) ^ (c + 1) * ((n : ℤ) + 4)) ≤ b + 2 := by omega
      have hcred : (2 : ℤ) ^ (nxw (List.replicate c .X) + 1) ≤ b + 2 := by
        rw [nxw_Xrun]
        have h1 : (1 : ℤ) ≤ (n : ℤ) + 4 := by omega
        have h2 : ((2 : ℤ) ^ (c + 1)) * 1 ≤ 2 ^ (c + 1) * ((n : ℤ) + 4) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        omega
      have hcr := rrun_credit (List.replicate c .X) (digs_Xrun c) b hcred
      rw [nxw_Xrun] at hcr
      have hdiv : (2 : ℤ) * ((n : ℤ) + 4) ≤ (b + 2) / 2 ^ c := by
        rw [Int.le_ediv_iff_mul_le (by positivity)]
        calc (2 : ℤ) * ((n : ℤ) + 4) * 2 ^ c = 2 ^ (c + 1) * ((n : ℤ) + 4) := by ring
          _ ≤ b + 2 := hbig
      rw [rrun_append]
      have : ((2 * n + 4 : ℕ) : ℤ) = 2 * (n : ℤ) + 4 := by push_cast; ring
      rw [this]
      linarith

/-! ## The values of the two cores -/

theorem rrun_YcX (M : ℕ) (a : ℤ) :
    rrun (List.replicate (M + 1) .Y ++ cX) a = 2 ^ (M + 3) * (a + 1) - 10 := by
  rw [rrun_append, rrun_Yrun]
  set u : ℤ := 2 ^ M * (a + 1) with hu
  have h1 : (2 : ℤ) ^ (M + 1) * (a + 1) - 1 = 2 * u - 1 := by rw [hu]; ring
  rw [h1]
  show rrun [RB.X, RB.Y, RB.Y, RB.V] (2 * u - 1) = _
  simp only [rrun_cons, rrun_nil, rstep_X, rstep_Y, rstep_V]
  have h2 : (2 * u - 1) / 2 = u - 1 := by omega
  rw [h2, hu]
  ring

theorem rrun_YcV (M : ℕ) (a : ℤ) :
    rrun (List.replicate (M + 1) .Y ++ cV) a = 2 ^ (M + 5) * (a + 1) - 10 := by
  rw [rrun_append, rrun_Yrun]
  show rrun [RB.V, RB.Y, RB.Y, RB.V] (2 ^ (M + 1) * (a + 1) - 1) = _
  simp only [rrun_cons, rrun_nil, rstep_Y, rstep_V]
  ring

theorem two_pow_le_int {i j : ℕ} (h : i ≤ j) : (2 : ℤ) ^ i ≤ 2 ^ j :=
  pow_le_pow_right₀ (by norm_num) h

/-! ## The core of every exceptional scan -/

/-- The shape all six families share: a run of pops whose exit debt is
divisible by four, over a core ending `Y V`. -/
theorem scan_core (u : List RB) (c : ℕ) {n m : ℕ} (hm : m + 4 = 2 ^ c * (n + 4))
    (hmod : m % 4 = 0) (hb : (m : ℤ) + 4 ≤ rrun (u ++ [.Y, .V]) a + 2) :
    Scan ((u ++ [.Y, .V]) ++ List.replicate c .X) n a Q :=
  scan_Xrun c hm hb (scan_stop_YV u hmod)

/-! ## The four shapes -/

/-- Families 1 and 2: the unextended `w0 2` with one bits in front. -/
theorem scan_fam12 (k : ℕ) : Scan (List.replicate (k + 1) .Y ++ cX) 0 a Q := by
  rw [show List.replicate (k + 1) RB.Y ++ cX
      = (List.replicate (k + 1) RB.Y ++ [RB.X, RB.Y]) ++ [RB.Y, RB.V] by simp [cX]]
  exact scan_stop_YV _ (by omega)

/-- Families 3 and 4: one marker step on the unextended `w0 2`. -/
theorem scan_fam34 (j k : ℕ) (ha : 0 ≤ a) :
    Scan (List.replicate (j + k + 2) .Y ++ (cX ++ List.replicate (k + 1) .X ++ [.V]))
      0 a Q := by
  have ht : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [show List.replicate (j + k + 2) RB.Y ++ (cX ++ List.replicate (k + 1) RB.X ++ [RB.V])
      = (((List.replicate (j + k + 2) RB.Y ++ [RB.X, RB.Y]) ++ [RB.Y, RB.V])
          ++ List.replicate (k + 1) RB.X) ++ [RB.V] by simp [cX]]
  refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
  refine scan_core _ (k + 1) (m := 2 ^ (k + 1) * 4 - 4) (by omega) (by omega) ?_
  have hmz : ((2 ^ (k + 1) * 4 - 4 : ℕ) : ℤ) + 4 = 4 * 2 ^ (k + 1) := by
    have h : ((2 ^ (k + 1) * 4 - 4 : ℕ) : ℤ) = (2 : ℤ) ^ (k + 1) * 4 - 4 := by
      push_cast [Nat.cast_sub (by omega : (4 : ℕ) ≤ 2 ^ (k + 1) * 4)]
      ring
    rw [h]; ring
  rw [hmz, show (List.replicate (j + k + 2) RB.Y ++ [RB.X, RB.Y]) ++ [RB.Y, RB.V]
      = List.replicate ((j + k + 1) + 1) RB.Y ++ cX by
        rw [show (j + k + 1) + 1 = j + k + 2 from rfl]; simp [cX], rrun_YcX,
    show j + k + 1 + 3 = j + k + 4 by omega]
  have h1 : (1 : ℤ) ≤ a + 1 := by omega
  have h3 : (2 : ℤ) ^ (j + k + 4) ≤ 2 ^ (j + k + 4) * (a + 1) :=
    le_mul_of_one_le_right (by positivity) h1
  have h2 : (2 : ℤ) ^ (k + 4) ≤ 2 ^ (j + k + 4) := two_pow_le_int (by omega)
  have h6 : (8 : ℤ) ≤ 2 ^ (k + 3) := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := two_pow_le_int (by omega)
  have h4 : (4 : ℤ) * 2 ^ (k + 1) = 2 ^ (k + 3) := by ring
  have h5 : (2 : ℤ) ^ (k + 4) = 2 * 2 ^ (k + 3) := by ring
  linarith

/-- Family 5: one marker step on the unextended `w0 3`. -/
theorem scan_fam5 (k : ℕ) (ha : 0 ≤ a) :
    Scan (List.replicate (k + 3) .Y ++ (cV ++ List.replicate (k + 2) .X ++ [.V]))
      0 a Q := by
  have ht : (1 : ℕ) ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
  rw [show List.replicate (k + 3) RB.Y ++ (cV ++ List.replicate (k + 2) RB.X ++ [RB.V])
      = (((List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y]) ++ [RB.Y, RB.V])
          ++ List.replicate (k + 2) RB.X) ++ [RB.V] by simp [cV]]
  refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
  refine scan_core _ (k + 2) (m := 2 ^ (k + 2) * 4 - 4) (by omega) (by omega) ?_
  have hmz : ((2 ^ (k + 2) * 4 - 4 : ℕ) : ℤ) + 4 = 4 * 2 ^ (k + 2) := by
    have h : ((2 ^ (k + 2) * 4 - 4 : ℕ) : ℤ) = (2 : ℤ) ^ (k + 2) * 4 - 4 := by
      push_cast [Nat.cast_sub (by omega : (4 : ℕ) ≤ 2 ^ (k + 2) * 4)]
      ring
    rw [h]; ring
  rw [hmz, show (List.replicate (k + 3) RB.Y ++ [RB.V, RB.Y]) ++ [RB.Y, RB.V]
      = List.replicate ((k + 2) + 1) RB.Y ++ cV by
        rw [show (k + 2) + 1 = k + 3 from rfl]; simp [cV], rrun_YcV,
    show k + 2 + 5 = k + 7 by omega]
  have h1 : (1 : ℤ) ≤ a + 1 := by omega
  have h3 : (2 : ℤ) ^ (k + 7) ≤ 2 ^ (k + 7) * (a + 1) :=
    le_mul_of_one_le_right (by positivity) h1
  have h4 : (4 : ℤ) * 2 ^ (k + 2) = 2 ^ (k + 4) := by ring
  have h5 : (2 : ℤ) ^ (k + 7) = 8 * 2 ^ (k + 4) := by ring
  have h6 : (8 : ℤ) ≤ 2 ^ (k + 4) := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 4) := two_pow_le_int (by omega)
  linarith

/-- The head `Y^L X Y` of the words of families 3, 4 and 6: the core `Y V`
that stops their scans is what follows it. -/
def headX (L : ℕ) : List RB := List.replicate L .Y ++ [.X, .Y]

theorem rrun_headX (M : ℕ) (a : ℤ) :
    rrun (headX (M + 1) ++ [.Y, .V]) a = 2 ^ (M + 3) * (a + 1) - 10 := by
  rw [show headX (M + 1) ++ [RB.Y, RB.V] = List.replicate (M + 1) RB.Y ++ cX by
    simp [headX, cX], rrun_YcX]

/-- Family 6: two marker steps on the unextended `w0 2`. -/
theorem scan_fam6 (j k : ℕ) (ha : 0 ≤ a) :
    Scan (List.replicate (j + k + 3) .Y ++
      (cX ++ List.replicate (k + 1) .X ++ [.V] ++ List.replicate j .X ++ [.V])) 0 a Q := by
  have hbv : rrun (headX (j + k + 3) ++ [.Y, .V]) a = 2 ^ (j + k + 5) * (a + 1) - 10 := by
    rw [show j + k + 3 = (j + k + 2) + 1 from rfl, rrun_headX,
      show j + k + 2 + 3 = j + k + 5 by omega]
  have ha1 : (1 : ℤ) ≤ a + 1 := by omega
  have hmul : (2 : ℤ) ^ (j + k + 5) ≤ 2 ^ (j + k + 5) * (a + 1) :=
    le_mul_of_one_le_right (by positivity) ha1
  have hfour : (4 : ℤ) ≤ 2 ^ (j + k + 2) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + k + 2) := two_pow_le_int (by omega)
  have hb5 : (2 : ℤ) ^ (j + k + 5) = 8 * 2 ^ (j + k + 2) := by ring
  have htj : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
  have hsk : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  -- the word, split at its two trailing zero bits
  rw [show List.replicate (j + k + 3) RB.Y ++
      (cX ++ List.replicate (k + 1) RB.X ++ [RB.V] ++ List.replicate j RB.X ++ [RB.V])
      = (((((headX (j + k + 3) ++ [RB.Y, RB.V]) ++ List.replicate (k + 1) RB.X) ++ [RB.V])
          ++ List.replicate j RB.X) ++ [RB.V]) by simp [headX, cX]]
  refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
  -- the outer run of `j` pops
  refine scan_Xrun j (m := 2 ^ j * 4 - 4) (by omega) ?_ ?_
  · -- its supply, from the credit of the part in front of it
    have hp : Digs (List.replicate (k + 1) RB.X ++ [RB.V]) :=
      (digs_Xrun (k + 1)).append (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)
    have hnx : nxw (List.replicate (k + 1) RB.X ++ [RB.V]) = k + 1 := by
      rw [nxw_append, nxw_Xrun]; rfl
    have hcond : (2 : ℤ) ^ (nxw (List.replicate (k + 1) RB.X ++ [RB.V]) + 1)
        ≤ rrun (headX (j + k + 3) ++ [.Y, .V]) a + 2 := by
      rw [hnx, hbv]
      have : (2 : ℤ) ^ (k + 2) ≤ 2 ^ (j + k + 2) := two_pow_le_int (by omega)
      linarith
    have hcr := rrun_credit _ hp (rrun (headX (j + k + 3) ++ [.Y, .V]) a) hcond
    rw [hnx] at hcr
    have hdiv : (4 : ℤ) * 2 ^ j
        ≤ (rrun (headX (j + k + 3) ++ [.Y, .V]) a + 2) / 2 ^ (k + 1) := by
      rw [Int.le_ediv_iff_mul_le (by positivity), hbv]
      have h1 : (4 : ℤ) * 2 ^ j * 2 ^ (k + 1) = 2 * 2 ^ (j + k + 2) := by ring
      linarith
    have hcast : ((2 ^ j * 4 - 4 : ℕ) : ℤ) + 4 = 4 * 2 ^ j := by
      have h : ((2 ^ j * 4 - 4 : ℕ) : ℤ) = (2 : ℤ) ^ j * 4 - 4 := by
        push_cast [Nat.cast_sub (by omega : (4 : ℕ) ≤ 2 ^ j * 4)]
        ring
      rw [h]; ring
    rw [hcast, show ((headX (j + k + 3) ++ [RB.Y, RB.V]) ++ List.replicate (k + 1) RB.X)
        ++ [RB.V] = (headX (j + k + 3) ++ [RB.Y, RB.V])
          ++ (List.replicate (k + 1) RB.X ++ [RB.V]) by simp, rrun_append]
    linarith
  · -- the zero bit between the two runs, and then the inner run of `k+1` pops
    refine Scan_snoc_V.mpr (Or.inr ⟨by omega, ?_⟩)
    have hn1 : (2 ^ j * 4 - 4) / 2 + 4 = 2 * 2 ^ j + 2 := by omega
    have hle : 4 ≤ 2 ^ (k + 1) * (2 * 2 ^ j + 2) := by
      have h := Nat.mul_le_mul hsk (show 4 ≤ 2 * 2 ^ j + 2 by omega)
      simpa using h
    refine scan_core (headX (j + k + 3)) (k + 1)
      (m := 2 ^ (k + 1) * (2 * 2 ^ j + 2) - 4) ?_ ?_ ?_
    · rw [hn1]; exact Nat.sub_add_cancel hle
    · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ 2 ^ (k + 1) * (2 * 2 ^ j + 2) :=
        ⟨2 ^ k * (2 ^ j + 1), by ring⟩
      omega
    · have hcast : ((2 ^ (k + 1) * (2 * 2 ^ j + 2) - 4 : ℕ) : ℤ) + 4
          = (2 : ℤ) ^ (k + 1) * (2 * 2 ^ j + 2) := by
        have h : ((2 ^ (k + 1) * (2 * 2 ^ j + 2) - 4 : ℕ) : ℤ)
            = (2 : ℤ) ^ (k + 1) * (2 * 2 ^ j + 2) - 4 := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [h]; ring
      rw [hcast, hbv]
      have h1 : (2 : ℤ) ^ (k + 1) * (2 * 2 ^ j + 2) = 2 ^ (j + k + 2) + 2 ^ (k + 2) := by
        ring
      have h2 : (2 : ℤ) ^ (k + 2) ≤ 2 ^ (j + k + 2) := two_pow_le_int (by omega)
      linarith

end BB25.Prefix
