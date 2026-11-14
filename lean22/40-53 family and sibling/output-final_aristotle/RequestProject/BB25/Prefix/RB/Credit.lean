/-
# The credit estimate and the leading-run criterion

Two elementary estimates on a reset word, and the criterion they give.

* **Forward credit.**  In the coordinate `C = value + 2` the three reset maps
  read `Y : C ↦ 2C-1`, `V : C ↦ 2C-2` and `X : C ↦ C/2`.  So a pop at worst
  halves the credit and a bit never decreases it: after a word with `j` pops
  the credit is at least `C₀ / 2^j` (`rrun_credit`).  In particular a word with
  enough starting credit is clean.

* **Reverse debt.**  Read backwards, the debt `n` satisfies `n+4 ↦ 2(n+4)` at a
  pop and never increases at a bit, so after crossing `K` pops it obeys
  `n + 4 ≤ 4·2^K` (this is carried through `scan_tail`).

Putting them together: at a pop with `K` pops already crossed the scan asks for
`2n+4 ≤ 2^(K+3)-4`, and the credit estimate delivers `2^(K+3)-2`.  So the whole
tail is supplied as soon as the part in front of it has credit `2^(J+2)`, `J`
the number of pops in the tail.

* **The leading run.**  Crossing `L` one bits in a row costs the scan a debt of
  at least `2^L - 1`, because the debt is halved and must stay odd.  A word
  `Y^L s` whose tail has `J ≤ L - 2` pops therefore always stops inside itself:
  the debt reaching the run is at most `2^(J+2) - 4 < 2^L - 1`
  (`scan_leading_run`).
-/
import RequestProject.BB25.Prefix.RB.Debt

namespace BB25.Prefix

open BB25

/-! ## Counting the pops of a word -/

/-- The number of pops (`X` letters) of a reset word. -/
def nxw : List RB → ℕ
  | [] => 0
  | .X :: t => nxw t + 1
  | _ :: t => nxw t

@[simp] theorem nxw_nil : nxw [] = 0 := rfl
@[simp] theorem nxw_X (t : List RB) : nxw (.X :: t) = nxw t + 1 := rfl
@[simp] theorem nxw_Y (t : List RB) : nxw (.Y :: t) = nxw t := rfl
@[simp] theorem nxw_V (t : List RB) : nxw (.V :: t) = nxw t := rfl

theorem nxw_append (u v : List RB) : nxw (u ++ v) = nxw u + nxw v := by
  induction u with
  | nil => simp
  | cons b u ih => cases b <;> simp [nxw, ih, Nat.add_right_comm]

@[simp] theorem nxw_Yrun (L : ℕ) : nxw (List.replicate L .Y) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => rw [List.replicate_succ]; simpa using ih

theorem digs_Yrun (L : ℕ) : Digs (List.replicate L .Y) := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact Or.inl rfl

/-- The value of a run of one bits. -/
theorem rrun_Yrun (L : ℕ) (a : ℤ) : rrun (List.replicate L .Y) a = 2 ^ L * (a + 1) - 1 := by
  induction L generalizing a with
  | zero => simp
  | succ L ih =>
      rw [List.replicate_succ, rrun_cons, rstep_Y, ih, pow_succ]
      ring

/-! ## The forward credit estimate -/

/-- **The credit estimate.**  A pop at worst halves the credit `value + 2`, and
a bit never decreases it. -/
theorem rrun_credit : ∀ (p : List RB), Digs p → ∀ (b : ℤ), 2 ^ (nxw p + 1) ≤ b + 2 →
    (b + 2) / 2 ^ (nxw p) ≤ rrun p b + 2 := by
  intro p
  induction p with
  | nil => intro _ b _; simp
  | cons c p ih =>
      intro hp b hb
      obtain ⟨hc, hp'⟩ := hp.of_cons
      have hb0 : (0 : ℤ) ≤ b := by
        have h2 : (2 : ℤ) ≤ 2 ^ (nxw (c :: p) + 1) := by
          calc (2 : ℤ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (nxw (c :: p) + 1) := by
                exact pow_le_pow_right₀ (by norm_num) (by omega)
        omega
      rcases hc with rfl | rfl | rfl
      · -- `Y`
        have hnx : nxw (RB.Y :: p) = nxw p := rfl
        have hb' : 2 ^ (nxw p + 1) ≤ (2 * b + 1) + 2 := by rw [hnx] at hb; omega
        have hmono : (b + 2) / 2 ^ (nxw p) ≤ ((2 * b + 1) + 2) / 2 ^ (nxw p) :=
          Int.ediv_le_ediv (by positivity) (by omega)
        rw [rrun_cons, rstep_Y, hnx]
        exact le_trans hmono (ih hp' (2 * b + 1) hb')
      · -- `V`
        have hnx : nxw (RB.V :: p) = nxw p := rfl
        have hb' : 2 ^ (nxw p + 1) ≤ 2 * b + 2 := by rw [hnx] at hb; omega
        have hmono : (b + 2) / 2 ^ (nxw p) ≤ (2 * b + 2) / 2 ^ (nxw p) :=
          Int.ediv_le_ediv (by positivity) (by omega)
        rw [rrun_cons, rstep_V, hnx]
        exact le_trans hmono (ih hp' (2 * b) hb')
      · -- `X`
        have hnx : nxw (RB.X :: p) = nxw p + 1 := rfl
        rw [hnx] at hb
        have hhalf : (b + 2) / 2 = b / 2 + 1 := by omega
        have hb' : 2 ^ (nxw p + 1) ≤ (b / 2 - 1) + 2 := by
          have h2 : (2 : ℤ) ^ (nxw p + 2) = 2 * 2 ^ (nxw p + 1) := by ring
          omega
        have hstep : (b + 2) / 2 ^ (nxw p + 1) = ((b / 2 - 1) + 2) / 2 ^ (nxw p) := by
          rw [show (2 : ℤ) ^ (nxw p + 1) = 2 * 2 ^ (nxw p) by ring,
            ← Int.ediv_ediv_of_nonneg (by positivity), hhalf]
          congr 1
          omega
        rw [rrun_cons, rstep_X, hnx, hstep]
        exact ih hp' (b / 2 - 1) hb'

/-! ## The scan of a supplied tail -/

/-- **The tail estimate.**  The scan of a tail whose pops are all supplied by
the credit of the part in front of it reaches that part with a debt bounded by
the number of pops it has crossed. -/
theorem scan_tail : ∀ (s : List RB), Digs s → ∀ (pre : List RB) (a : ℤ) (n K : ℕ)
    (Q : ℕ → Prop), Digs pre → n + 4 ≤ 4 * 2 ^ K →
    2 ^ (nxw s + K + 2) ≤ rrun pre a + 2 →
    (∀ m : ℕ, m + 4 ≤ 4 * 2 ^ (K + nxw s) → Scan pre m a Q) →
    Scan (pre ++ s) n a Q := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
      intro _ pre a n K Q _ hn _ hQ
      simpa using hQ n (by simpa using hn)
  | append_singleton t c ih =>
      intro hs pre a n K Q hpre hn hcred hQ
      obtain ⟨ht, hc1⟩ := hs.of_append
      have hc : Dig c := hc1 c (by simp)
      have hassoc : pre ++ (t ++ [c]) = (pre ++ t) ++ [c] := by simp
      rw [hassoc]
      rcases hc with rfl | rfl | rfl
      · -- a one bit
        have hnx : nxw (t ++ [RB.Y]) = nxw t := by rw [nxw_append]; simp
        rw [hnx] at hcred hQ
        refine Scan_snoc_Y.mpr ?_
        by_cases hpar : n % 2 = 0
        · exact Or.inl hpar
        · exact Or.inr ⟨by omega, ih ht pre a _ K Q hpre (by omega) hcred hQ⟩
      · -- a zero bit
        have hnx : nxw (t ++ [RB.V]) = nxw t := by rw [nxw_append]; simp
        rw [hnx] at hcred hQ
        refine Scan_snoc_V.mpr ?_
        by_cases hpar : n % 2 = 1
        · exact Or.inl hpar
        · exact Or.inr ⟨by omega, ih ht pre a _ K Q hpre (by omega) hcred hQ⟩
      · -- a pop
        have hnx : nxw (t ++ [RB.X]) = nxw t + 1 := by rw [nxw_append]; simp
        rw [hnx, show nxw t + 1 + K + 2 = nxw t + K + 3 by omega] at hcred
        rw [hnx] at hQ
        -- the supply
        have hb0 : 2 ^ (nxw t + 1) ≤ rrun pre a + 2 := by
          have hmono : (2 : ℤ) ^ (nxw t + 1) ≤ 2 ^ (nxw t + K + 3) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          omega
        have hcr := rrun_credit t ht (rrun pre a) hb0
        have hbig : (2 : ℤ) ^ (K + 3) ≤ (rrun pre a + 2) / 2 ^ (nxw t) := by
          have h1 : (2 : ℤ) ^ (nxw t + K + 3) / 2 ^ (nxw t) ≤ (rrun pre a + 2) / 2 ^ (nxw t) :=
            Int.ediv_le_ediv (by positivity) hcred
          rwa [show (2 : ℤ) ^ (nxw t + K + 3) = 2 ^ (nxw t) * 2 ^ (K + 3) by ring,
            Int.mul_ediv_cancel_left _ (by positivity)] at h1
        have hsup : ((2 * n + 4 : ℕ) : ℤ) ≤ rrun (pre ++ t) a := by
          rw [rrun_append]
          have hnb : ((n : ℤ) + 4) ≤ 4 * 2 ^ K := by exact_mod_cast hn
          have h4 : ((2 * n + 4 : ℕ) : ℤ) = 2 * ((n : ℤ) + 4) - 4 := by push_cast; ring
          have hpow : (2 : ℤ) ^ (K + 3) = 8 * 2 ^ K := by ring
          omega
        refine Scan_snoc_X.mpr ⟨hsup, ?_⟩
        refine ih ht pre a _ (K + 1) Q hpre (by
          have : n + 4 ≤ 4 * 2 ^ K := hn
          have : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
          omega) ?_ ?_
        · rw [show nxw t + (K + 1) + 2 = nxw t + K + 3 by omega]
          exact hcred
        · intro m hm
          exact hQ m (by rw [show K + 1 + nxw t = K + (nxw t + 1) by omega] at hm; exact hm)

/-! ## The leading run -/

/-- **Crossing a run of one bits costs `2^L - 1`.**  So a debt below that stops
inside the run. -/
theorem scan_Yrun : ∀ (L : ℕ), 1 ≤ L → ∀ (m : ℕ) (a : ℤ) (Q : ℕ → Prop), m + 2 ≤ 2 ^ L →
    Scan (List.replicate L .Y) m a Q := by
  intro L
  induction L with
  | zero => intro h; omega
  | succ L ih =>
      intro _ m a Q hm
      rw [List.replicate_succ']
      refine Scan_snoc_Y.mpr ?_
      by_cases hpar : m % 2 = 0
      · exact Or.inl hpar
      · rcases Nat.eq_zero_or_pos L with rfl | hL
        · -- a single one bit and an odd debt is impossible
          have : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
          omega
        · refine Or.inr ⟨by omega, ih hL _ a Q ?_⟩
          have : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
          omega

/-! ## The criterion -/

/-- **The leading-run criterion.**  A reset word that begins with a run of `L`
one bits and has at most `L - 2` pops after it always stops its own scan. -/
theorem scan_leading_run {L : ℕ} {s : List RB} (hs : Digs s) {a : ℤ} (ha : 0 ≤ a)
    (hL : nxw s + 2 ≤ L) :
    Scan (List.replicate L .Y ++ s) 0 a (fun _ => False) := by
  have hpow : ((2 : ℤ) ^ (nxw s + 2)) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
  have hval : rrun (List.replicate L .Y) a = 2 ^ L * (a + 1) - 1 := rrun_Yrun L a
  have hL1 : 1 ≤ L := by omega
  refine scan_tail s hs _ a 0 0 _ (digs_Yrun L) (by norm_num) ?_ ?_
  · rw [hval, show nxw s + 0 + 2 = nxw s + 2 by omega]
    have h1 : (1 : ℤ) ≤ a + 1 := by omega
    have h2 : (2 : ℤ) ^ L ≤ 2 ^ L * (a + 1) := le_mul_of_one_le_right (by positivity) h1
    omega
  · intro m hm
    rw [show 0 + nxw s = nxw s by omega] at hm
    refine scan_Yrun L hL1 m a _ ?_
    have h4 : (4 : ℕ) * 2 ^ nxw s = 2 ^ (nxw s + 2) := by ring
    have h5 : (2 : ℕ) ^ (nxw s + 2) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
    omega

/-- The value of a word covered by the leading-run criterion is positive. -/
theorem rrun_pos_leading_run {L : ℕ} {s : List RB} (hs : Digs s) {a : ℤ} (ha : 0 ≤ a)
    (hL : nxw s + 2 ≤ L) : 2 ≤ rrun (List.replicate L .Y ++ s) a := by
  set b := rrun (List.replicate L .Y) a with hb
  have hval : b = 2 ^ L * (a + 1) - 1 := rrun_Yrun L a
  have h1 : (1 : ℤ) ≤ a + 1 := by omega
  have hbig : (2 : ℤ) ^ (nxw s + 2) ≤ b + 2 := by
    have h2 : (2 : ℤ) ^ L ≤ 2 ^ L * (a + 1) := le_mul_of_one_le_right (by positivity) h1
    have h3 : ((2 : ℤ) ^ (nxw s + 2)) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
    omega
  have hcr := rrun_credit s hs b (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hbig)
  have h4 : (4 : ℤ) ≤ (b + 2) / 2 ^ (nxw s) := by
    have h1' : (2 : ℤ) ^ (nxw s + 2) / 2 ^ (nxw s) ≤ (b + 2) / 2 ^ (nxw s) :=
      Int.ediv_le_ediv (by positivity) hbig
    rwa [show (2 : ℤ) ^ (nxw s + 2) = 2 ^ (nxw s) * 4 by ring,
      Int.mul_ediv_cancel_left _ (by positivity)] at h1'
  rw [rrun_append, ← hb]
  omega

end BB25.Prefix
