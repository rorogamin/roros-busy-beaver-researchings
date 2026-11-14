/-
# The general expanding-close bound, and the dyadic slack of a clean prefix

`Expand.lean` proves the three bounds

```
              2 ^ h * (c + 1)      - 1 ≤ trun w a c
  1 ≤ q  →    2 ^ h * (4 c + 3)    - 1 ≤ trun w a c
  2 ≤ q  →    2 ^ h * (16 c + 11)  - 1 ≤ trun w a c
```

for a Dyck prefix of height `h` with `q` expanding closes.  The constants
`c + 1`, `4c + 3`, `16c + 11` are the first values of

```
  qgain 0 c = c + 1,        qgain (q+1) c = 4 * qgain q c - 1,
```

and this file proves the bound for **every** `q`:

```
  q ≤ qcnt w a  →  2 ^ h * qgain q c ≤ trun w a c + 1.
```

Together with the matching upper bound on the *first* counter

```
  rrun w a + 1 ≤ 2 ^ (h + 2 * qcnt w a) * (a + 1)
```

it gives the result the early cases of the `0RB` branch need: if the value of
a clean nonempty Dyck prefix of height at least one is a power of two, then
its transduced value exceeds it by at least two (`trun_gt_of_pow`).  This is
Lemma B of the submitted argument.
-/
import RequestProject.BB25.Prefix.Expand

namespace BB25.Prefix

open BB25

/-! ## The constants of the general bound -/

/-- The loss `(4 ^ q - 1) / 3` of the general bound. -/
def qloss : ℕ → ℤ
  | 0 => 0
  | q + 1 => 4 * qloss q + 1

@[simp] theorem qloss_zero : qloss 0 = 0 := rfl
theorem qloss_succ (q : ℕ) : qloss (q + 1) = 4 * qloss q + 1 := rfl

theorem qloss_nonneg : ∀ q : ℕ, 0 ≤ qloss q
  | 0 => le_refl _
  | q + 1 => by rw [qloss_succ]; have := qloss_nonneg q; omega

theorem qloss_one_le {q : ℕ} (hq : 1 ≤ q) : 1 ≤ qloss q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [qloss_succ]
  have := qloss_nonneg p
  omega

theorem qloss_add (i j : ℕ) : qloss (i + j) = 4 ^ j * qloss i + qloss j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show i + (j + 1) = (i + j) + 1 by omega, qloss_succ, ih, qloss_succ, pow_succ]
      ring

/-- The gain of a Dyck prefix with `q` expanding closes: the constant
`(2 * 4 ^ q + 1) / 3` of the general bound, at second counter `c`. -/
def qgain (q : ℕ) (c : ℤ) : ℤ := 4 ^ q * (c + 1) - qloss q

theorem qgain_zero (c : ℤ) : qgain 0 c = c + 1 := by simp [qgain]

theorem qgain_succ (q : ℕ) (c : ℤ) : qgain (q + 1) c = 4 * qgain q c - 1 := by
  simp only [qgain, qloss_succ, pow_succ]
  ring

theorem qgain_one_le {c : ℤ} (hc : 0 ≤ c) : ∀ q : ℕ, 1 ≤ qgain q c := by
  intro q
  induction q with
  | zero => rw [qgain_zero]; omega
  | succ q ih => rw [qgain_succ]; omega

theorem qgain_mono {c : ℤ} (hc : 0 ≤ c) {q Q : ℕ} (h : q ≤ Q) : qgain q c ≤ qgain Q c := by
  obtain ⟨d, rfl⟩ : ∃ d, Q = q + d := ⟨Q - q, by omega⟩
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
      have h1 := qgain_one_le hc (q + d)
      rw [show q + (d + 1) = (q + d) + 1 by omega, qgain_succ]
      omega

/-- Splitting the gain: each expanding close of a suffix multiplies the gain of
the prefix by four. -/
theorem qgain_add (i j : ℕ) (c : ℤ) : qgain (i + j) c = 4 ^ j * qgain i c - qloss j := by
  simp only [qgain, qloss_add i j, pow_add]
  ring

/-- The gain of a doubled second counter. -/
theorem qgain_double (j : ℕ) (c : ℤ) : qgain j (2 * c + 1) = 2 * (4 ^ j * (c + 1)) - qloss j := by
  simp only [qgain]
  ring

/-! ## The general bound -/

private theorem trun_gain_aux : ∀ (n : ℕ) (w : List RB), w.length ≤ n → Digs w → DyckPre w →
    ∀ (h : ℕ), bal w = (h : ℤ) → ∀ a c : ℤ, 0 ≤ c → ∀ q : ℕ, q ≤ qcnt w a →
      2 ^ h * qgain q c ≤ trun w a c + 1 := by
  intro n
  induction n with
  | zero =>
      intro w hlen _ _ h hbal a c hc q hq
      obtain rfl : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simp only [bal_nil] at hbal
      obtain rfl : h = 0 := by exact_mod_cast hbal.symm
      simp only [qcnt_nil, Nat.le_zero] at hq
      subst hq
      simp only [trun_nil, pow_zero, one_mul, qgain_zero]
      omega
  | succ n ih =>
      intro w hlen hdigs hd h hbal a c hc q hq
      rcases List.eq_nil_or_concat w with rfl | ⟨p, b, hcat⟩
      · simp only [bal_nil] at hbal
        obtain rfl : h = 0 := by exact_mod_cast hbal.symm
        simp only [qcnt_nil, Nat.le_zero] at hq
        subst hq
        simp only [trun_nil, pow_zero, one_mul, qgain_zero]
        omega
      rw [List.concat_eq_append] at hcat
      subst hcat
      have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
      have hdigsp : Digs p := (hdigs.of_append).1
      have hlenp : p.length ≤ n := by
        have : (p ++ [b]).length = p.length + 1 := by simp
        omega
      have hbb : Dig b := (hdigs.of_append).2 b (by simp)
      have hbalsum : bal (p ++ [b]) = bal p + bal [b] := bal_append p [b]
      have htsplit : trun (p ++ [b]) a c = rstep (qout b (rrun p a)) (trun p a c) := by
        rw [trun_append]; simp
      have hqsplit : qcnt (p ++ [b]) a = qcnt p a + qstep b (rrun p a) := by
        rw [qcnt_append]; simp
      have hP : (1 : ℤ) ≤ 2 ^ h := by
        have : (0 : ℤ) < 2 ^ h := by positivity
        omega
      have hgn : ∀ H Q : ℕ, (1 : ℤ) ≤ 2 ^ H * qgain Q c := by
        intro H Q
        have h1 : (1 : ℤ) ≤ 2 ^ H := by
          have : (0 : ℤ) < 2 ^ H := by positivity
          omega
        have h2 := qgain_one_le hc Q
        nlinarith
      rcases hbb with rfl | rfl | rfl
      · -- an opening `Y`
        have hbp : bal p = (h : ℤ) - 1 := by simp [bal] at hbalsum; omega
        have hh : 1 ≤ h := by
          have := hdp.bal_nonneg
          omega
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        have hbp' : bal p = (h' : ℤ) := by push_cast at hbp ⊢; omega
        have hq' : q ≤ qcnt p a := by rw [hqsplit] at hq; simpa using hq
        have A := ih p hlenp hdigsp hdp h' hbp' a c hc q hq'
        rw [htsplit]
        simp only [qout, rstep_Y]
        have e2 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
        rw [e2]
        linarith
      · -- a closing `V`: always expanding
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have hqv : qcnt (p ++ [RB.V]) a = qcnt p a + 1 := by rw [hqsplit]; simp
        have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        rw [htsplit]
        simp only [qout, rstep_Y]
        rcases Nat.lt_or_ge (qcnt p a) q with hlt | hge
        · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          have hq'' : q' ≤ qcnt p a := by omega
          have A := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc q' hq''
          rw [e2] at A
          rw [qgain_succ]
          nlinarith [hP, A]
        · have A := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc q hge
          rw [e2] at A
          linarith [hgn h q]
      · -- a closing `X`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        by_cases hodd : (rrun p a) % 2 = 1
        · -- expanding
          have hqv : qcnt (p ++ [RB.X]) a = qcnt p a + 1 := by
            rw [hqsplit, qstep_X, if_pos hodd]
          rw [htsplit]
          simp only [qout, hodd, if_pos, rstep_V]
          rcases Nat.lt_or_ge (qcnt p a) q with hlt | hge
          · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
            have hq'' : q' ≤ qcnt p a := by rw [hqv] at hq; omega
            have A := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc q' hq''
            rw [e2] at A
            rw [qgain_succ]
            nlinarith [hP, A]
          · have A := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc q hge
            rw [e2] at A
            linarith [hgn h q]
        · -- contracting: split the last matched group off
          have hbalp : 1 ≤ bal p := by omega
          obtain ⟨u, e, rfl, hdu, hbe⟩ := dyck_split hdigsp hdp hbalp
          have hdigsu : Digs u := (hdigsp.of_append).1
          have hdigse : Digs e := ((hdigsp.of_append).2.of_cons).2
          have hlenu : u.length ≤ n := by
            have h1 : (u ++ RB.Y :: e).length = u.length + e.length + 1 := by simp; omega
            omega
          have hlene : e.length ≤ n := by
            have h1 : (u ++ RB.Y :: e).length = u.length + e.length + 1 := by simp; omega
            omega
          have hbu : bal u = (h : ℤ) := by
            rw [bal_append, bal_Y, hbe.2] at hbp
            omega
          set cu : ℤ := trun u a c with hcu
          set au : ℤ := rrun u a with hau
          set c₂ : ℤ := trun e (2 * au + 1) (2 * cu + 1) with hc₂
          set a₂ : ℤ := rrun e (2 * au + 1) with ha₂
          -- the interior is nonempty, so it contains an expanding close
          have hne : e ≠ [] := by
            rintro rfl
            simp only [ha₂, rrun_nil] at *
            have hr : rrun (u ++ RB.Y :: []) a = 2 * au + 1 := by
              rw [rrun_append, rrun_cons, rrun_nil, rstep_Y, ← hau]
            rw [hr] at hodd
            omega
          have hqe : 1 ≤ qcnt e (2 * au + 1) :=
            qcnt_pos_of_hasCl hdigse hbe.1 (HasCl.of_bal hdigse hbe hne) _
          -- the run and the value of the whole word
          have hrunw : rrun (u ++ RB.Y :: e) a = a₂ := by
            rw [rrun_append, rrun_cons, rstep_Y, ← hau, ← ha₂]
          have htrunw : trun (u ++ RB.Y :: e) a c = c₂ := by
            rw [trun_append, trun_cons, rstep_Y, ← hau, ← hcu]
            simp only [qout, rstep_Y, ← hc₂]
          have hqw : qcnt ((u ++ RB.Y :: e) ++ [RB.X]) a = qcnt u a + qcnt e (2 * au + 1) := by
            rw [hqsplit, qcnt_append, qcnt_cons, qstep_X, if_neg hodd, ← hau]
            simp
          have htw : trun ((u ++ RB.Y :: e) ++ [RB.X]) a c = c₂ / 2 - 1 := by
            rw [htsplit, htrunw, hrunw]
            have hqX : qout RB.X a₂ = RB.X := by
              simp only [qout]
              rw [if_neg]
              rw [hrunw] at hodd
              exact hodd
            rw [hqX, rstep_X]
          rw [htw]
          rw [hqw] at hq
          -- the split of the expanding closes: at least one is spent inside
          obtain ⟨q'', q', hq''A, hq'E, hq'1, hqsum⟩ :
              ∃ q'' q' : ℕ, q'' ≤ qcnt u a ∧ q' ≤ qcnt e (2 * au + 1) ∧ 1 ≤ q' ∧
                q ≤ q'' + q' := by
            rcases Nat.lt_or_ge (qcnt u a) q with hlt | hle
            · exact ⟨qcnt u a, q - qcnt u a, le_refl _, by omega, by omega, by omega⟩
            · exact ⟨q, 1, hle, hqe, le_refl 1, by omega⟩
          -- the two induction hypotheses
          have A := ih u hlenu hdigsu hdu h hbu a c hc q'' hq''A
          have hcu0 : 0 ≤ cu := by
            have := hgn h q''
            omega
          have B := ih e hlene hdigse hbe.1 0 (by simpa using hbe.2) (2 * au + 1)
            (2 * cu + 1) (by omega) q' hq'E
          rw [pow_zero, one_mul, qgain_double] at B
          have hE : (0 : ℤ) ≤ 4 ^ q' := by positivity
          have hM : (1 : ℤ) ≤ qloss q' := qloss_one_le hq'1
          have hgain : qgain q c ≤ 4 ^ q' * qgain q'' c - qloss q' := by
            calc qgain q c ≤ qgain (q'' + q') c := qgain_mono hc hqsum
              _ = 4 ^ q' * qgain q'' c - qloss q' := qgain_add _ _ _
          obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, Z = 4 ^ q' * (2 ^ h * qgain q'' c) := ⟨_, rfl⟩
          obtain ⟨PM, hPM⟩ : ∃ PM : ℤ, PM = 2 ^ h * qloss q' := ⟨_, rfl⟩
          obtain ⟨G, hG⟩ : ∃ G : ℤ, G = 2 ^ h * qgain q c := ⟨_, rfl⟩
          obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = qloss q' := ⟨_, rfl⟩
          have h1 : 2 * Z - M ≤ c₂ + 1 := by
            have hmul := mul_le_mul_of_nonneg_left A (show (0 : ℤ) ≤ 2 * 4 ^ q' by positivity)
            rw [hZ, hMdef]
            linarith only [hmul, B]
          have h2 : G ≤ Z - PM := by
            have hmul := mul_le_mul_of_nonneg_left hgain (show (0 : ℤ) ≤ 2 ^ h by positivity)
            rw [hG, hZ, hPM]
            linarith only [hmul]
          have h3 : (1 : ℤ) ≤ M := by rw [hMdef]; exact hM
          have h4 : M ≤ PM := by
            rw [hMdef, hPM]
            have := mul_le_mul_of_nonneg_right hP (le_trans zero_le_one hM)
            linarith only [this]
          rw [← hG]
          omega

/-- **The general expanding-close bound.**  A Dyck prefix of height `h` with at
least `q` expanding closes multiplies the second counter by `qgain q c`. -/
theorem trun_ge_qgain {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) {a c : ℤ} (hc : 0 ≤ c) {q : ℕ} (hq : q ≤ qcnt w a) :
    2 ^ h * qgain q c ≤ trun w a c + 1 :=
  trun_gain_aux w.length w (le_refl _) hw hd h hb a c hc q hq

/-! ## The matching upper bound on the first counter -/

private theorem rrun_le_aux : ∀ (n : ℕ) (w : List RB), w.length ≤ n → Digs w → DyckPre w →
    ∀ (h : ℕ), bal w = (h : ℤ) → ∀ a : ℤ, 0 ≤ a → 0 ≤ rrun w a →
      rrun w a + 1 ≤ 2 ^ (h + 2 * qcnt w a) * (a + 1) := by
  intro n
  induction n with
  | zero =>
      intro w hlen _ _ h hbal a ha hcl
      obtain rfl : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simp only [bal_nil] at hbal
      obtain rfl : h = 0 := by exact_mod_cast hbal.symm
      simp
  | succ n ih =>
      intro w hlen hdigs hd h hbal a ha hcl
      rcases List.eq_nil_or_concat w with rfl | ⟨p, b, hcat⟩
      · simp only [bal_nil] at hbal
        obtain rfl : h = 0 := by exact_mod_cast hbal.symm
        simp
      rw [List.concat_eq_append] at hcat
      subst hcat
      have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
      have hdigsp : Digs p := (hdigs.of_append).1
      have hlenp : p.length ≤ n := by
        have : (p ++ [b]).length = p.length + 1 := by simp
        omega
      have hbb : Dig b := (hdigs.of_append).2 b (by simp)
      have hbalsum : bal (p ++ [b]) = bal p + bal [b] := bal_append p [b]
      have hqsplit : qcnt (p ++ [b]) a = qcnt p a + qstep b (rrun p a) := by
        rw [qcnt_append]; simp
      have hrsplit : rrun (p ++ [b]) a = rstep b (rrun p a) := by
        rw [rrun_append]; simp
      have hclp : 0 ≤ rrun p a := by
        refine rrun_nonneg_of_nonneg (v := [b]) ?_ hcl
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact hbb
      rcases hbb with rfl | rfl | rfl
      · -- an opening `Y`
        have hbp : bal p = (h : ℤ) - 1 := by simp [bal] at hbalsum; omega
        have hh : 1 ≤ h := by have := hdp.bal_nonneg; omega
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        have hbp' : bal p = (h' : ℤ) := by push_cast at hbp ⊢; omega
        have A := ih p hlenp hdigsp hdp h' hbp' a ha hclp
        have hqY : qcnt (p ++ [RB.Y]) a = qcnt p a := by rw [hqsplit]; simp
        rw [hrsplit, hqY, rstep_Y]
        have e2 : (2 : ℤ) ^ (h' + 1 + 2 * qcnt p a) = 2 * 2 ^ (h' + 2 * qcnt p a) := by
          rw [show h' + 1 + 2 * qcnt p a = (h' + 2 * qcnt p a) + 1 by omega, pow_succ]
          ring
        rw [e2]
        linarith
      · -- a closing `V`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have A := ih p hlenp hdigsp hdp (h + 1) hbp' a ha hclp
        have hqV : qcnt (p ++ [RB.V]) a = qcnt p a + 1 := by rw [hqsplit]; simp
        rw [hrsplit, hqV, rstep_V]
        have e2 : (2 : ℤ) ^ (h + 2 * (qcnt p a + 1)) = 2 * 2 ^ (h + 1 + 2 * qcnt p a) := by
          rw [show h + 2 * (qcnt p a + 1) = (h + 1 + 2 * qcnt p a) + 1 by omega, pow_succ]
          ring
        rw [e2]
        linarith
      · -- a closing `X`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have A := ih p hlenp hdigsp hdp (h + 1) hbp' a ha hclp
        rw [hrsplit, rstep_X]
        by_cases hodd : (rrun p a) % 2 = 1
        · have hqX : qcnt (p ++ [RB.X]) a = qcnt p a + 1 := by
            rw [hqsplit, qstep_X, if_pos hodd]
          rw [hqX]
          have e2 : (2 : ℤ) ^ (h + 2 * (qcnt p a + 1)) = 2 * 2 ^ (h + 1 + 2 * qcnt p a) := by
            rw [show h + 2 * (qcnt p a + 1) = (h + 1 + 2 * qcnt p a) + 1 by omega, pow_succ]
            ring
          rw [e2]
          obtain ⟨R, hR⟩ : ∃ R : ℤ, R = 2 ^ (h + 1 + 2 * qcnt p a) * (a + 1) := ⟨_, rfl⟩
          rw [show (2 : ℤ) * 2 ^ (h + 1 + 2 * qcnt p a) * (a + 1)
            = 2 * (2 ^ (h + 1 + 2 * qcnt p a) * (a + 1)) by ring, ← hR]
          rw [← hR] at A
          omega
        · have hqX : qcnt (p ++ [RB.X]) a = qcnt p a := by
            rw [hqsplit, qstep_X, if_neg hodd]
            simp
          rw [hqX]
          have e2 : (2 : ℤ) ^ (h + 1 + 2 * qcnt p a) = 2 * 2 ^ (h + 2 * qcnt p a) := by
            rw [show h + 1 + 2 * qcnt p a = (h + 2 * qcnt p a) + 1 by omega, pow_succ]
            ring
          rw [e2] at A
          obtain ⟨R, hR⟩ : ∃ R : ℤ, R = 2 ^ (h + 2 * qcnt p a) * (a + 1) := ⟨_, rfl⟩
          rw [← hR]
          rw [show (2 : ℤ) * 2 ^ (h + 2 * qcnt p a) * (a + 1)
            = 2 * (2 ^ (h + 2 * qcnt p a) * (a + 1)) by ring, ← hR] at A
          omega

/-- **The first counter is bounded by the height and the expanding closes.** -/
theorem rrun_le_two_pow {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) {a : ℤ} (ha : 0 ≤ a) (hcl : 0 ≤ rrun w a) :
    rrun w a + 1 ≤ 2 ^ (h + 2 * qcnt w a) * (a + 1) :=
  rrun_le_aux w.length w (le_refl _) hw hd h hb a ha hcl

/-! ## Lemma B at the level of words -/

theorem three_qloss (q : ℕ) : 3 * qloss q = 4 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih => rw [qloss_succ, pow_succ]; omega

/-- Two powers of two differ by two only for `4 - 2`. -/
private theorem two_pow_diff_two {h e : ℕ} (hh : 1 ≤ h) (he : 1 ≤ e)
    (hval : (2 : ℤ) ^ h - 2 ^ e = 2) : h = 2 ∧ e = 1 := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hp1 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
  have hp2 : (2 : ℤ) ^ (e' + 1) = 2 * 2 ^ e' := by ring
  have hkey : (2 : ℤ) ^ h' - 2 ^ e' = 1 := by omega
  have h1 : (1 : ℤ) ≤ 2 ^ h' := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℤ) ≤ 2 ^ e' := one_le_pow₀ (by norm_num)
  rcases Nat.eq_zero_or_pos e' with rfl | he'
  · simp only [pow_zero] at hkey
    refine ⟨?_, rfl⟩
    rcases Nat.lt_or_ge h' 2 with hlt | hge
    · interval_cases h'
      · simp at hkey
      · rfl
    · exfalso
      have h4 : (4 : ℤ) ∣ 2 ^ h' := by
        obtain ⟨m, rfl⟩ : ∃ m, h' = m + 2 := ⟨h' - 2, by omega⟩
        exact ⟨2 ^ m, by ring⟩
      omega
  · exfalso
    have hd2 : (2 : ℤ) ∣ 2 ^ e' := dvd_pow_self 2 (by omega)
    rcases Nat.eq_zero_or_pos h' with rfl | hh'
    · simp only [pow_zero] at hkey
      omega
    · have hd1 : (2 : ℤ) ∣ 2 ^ h' := dvd_pow_self 2 (by omega)
      omega

/-- **Lemma B.**  If the value of a clean Dyck prefix of height at least one is
a power of two, then its transduced value exceeds it by at least two. -/
theorem trun_gt_of_pow {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) (hh : 1 ≤ h) {e : ℕ} (he : 1 ≤ e)
    (hval : rrun w 0 = 2 ^ e) : rrun w 0 + 2 ≤ trun w 0 0 := by
  have hpowe : (2 : ℤ) ≤ 2 ^ e := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
  have hf2 : (2 : ℤ) ≤ rrun w 0 := by rw [hval]; exact hpowe
  have hcl : (0 : ℤ) ≤ rrun w 0 := by omega
  have hde : (2 : ℤ) ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have hdh : (2 : ℤ) ∣ 2 ^ h := dvd_pow_self 2 (by omega)
  have hshape : Shape (rrun w 0) h (0 + qcnt w 0) := by
    refine shape_run w hw 0 0 0 (Or.inl ⟨rfl, by norm_num⟩) ?_ hcl h ?_
    · intro p hp
      simpa using hd p hp
    · simpa using hb.symm
  rcases hshape with ⟨-, hv0⟩ | ⟨hq1, k, hk, hv1⟩ | hq2
  · -- no expanding close: the value is `2 ^ h - 1`, which is odd
    rw [hval] at hv0
    omega
  · -- exactly one expanding close: the prefix is `Y Y V X`-like, of height two
    have hk0 : k = 0 := by
      by_contra hc
      have hdk : (2 : ℤ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have hdh2 : (2 : ℤ) ∣ 2 ^ (h + 2) := dvd_pow_self 2 (by omega)
      rw [hval] at hv1
      rcases hv1 with hv | hv <;> omega
    subst hk0
    simp only [pow_zero] at hv1
    rw [hval] at hv1
    have hboth : h = 2 ∧ e = 1 := by
      rcases hv1 with hv | hv
      · exact two_pow_diff_two hh he (by omega)
      · have := two_pow_diff_two (h := h + 2) (by omega) he (by omega)
        omega
    have hq : 1 ≤ qcnt w 0 := by omega
    have hbound := trun_ge_pow_q1 hw hd hb (le_refl (0 : ℤ)) hq
    rw [hboth.1] at hbound
    norm_num at hbound
    rw [hval, hboth.2]
    norm_num
    omega
  · -- at least two expanding closes: the general bound
    have hq2' : 2 ≤ qcnt w 0 := by omega
    have hup := rrun_le_two_pow hw hd hb (le_refl (0 : ℤ)) hcl
    rw [zero_add, mul_one] at hup
    have hbig : (32 : ℤ) ≤ 2 ^ (h + 2 * qcnt w 0) := by
      calc (32 : ℤ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (h + 2 * qcnt w 0) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hlt : (2 : ℤ) ^ e < 2 ^ (h + 2 * qcnt w 0) := by rw [← hval]; omega
    have helt : e < h + 2 * qcnt w 0 := (pow_lt_pow_iff_right₀ (by norm_num)).mp hlt
    have h2f : 2 * rrun w 0 ≤ 2 ^ (h + 2 * qcnt w 0) := by
      rw [hval]
      calc 2 * (2 : ℤ) ^ e = 2 ^ (e + 1) := by ring
        _ ≤ 2 ^ (h + 2 * qcnt w 0) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hPh : (2 : ℤ) ≤ 2 ^ h := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hh
    have hgain := trun_ge_qgain hw hd hb (le_refl (0 : ℤ)) (le_refl (qcnt w 0))
    have h3 : 3 * qgain (qcnt w 0) 0 = 2 * 4 ^ qcnt w 0 + 1 := by
      simp only [qgain]
      have := three_qloss (qcnt w 0)
      omega
    have hpowsplit : (2 : ℤ) ^ h * (2 * 4 ^ qcnt w 0 + 1)
        = 2 * 2 ^ (h + 2 * qcnt w 0) + 2 ^ h := by
      have h4 : (4 : ℤ) ^ qcnt w 0 = 2 ^ (2 * qcnt w 0) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [h4, pow_add]
      ring
    have hmul := mul_le_mul_of_nonneg_left hgain (show (0 : ℤ) ≤ 3 by norm_num)
    have hkey : 2 * 2 ^ (h + 2 * qcnt w 0) + 2 ^ h ≤ 3 * (trun w 0 0 + 1) := by
      rw [← hpowsplit, ← h3]
      linarith only [hmul]
    omega

end BB25.Prefix
