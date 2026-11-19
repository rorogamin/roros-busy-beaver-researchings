/-
  BB/BB6_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(6, 8):
    TM: 5RE3LB7LF2RA4LB6LF1RZ5RF_5LE3RB1LD2RA3LF7RC3LB3RA_3RB1LB3LC2RC4LC0LE6LE5LF_3RB6RD3LC2RC5LA3RE2LE1LB_5RC3RE2RA4LC6RA5LA2LE3RE_5RB7RD1LF1LF5RA5RF5LE0RD
    Domain: BB(6, 8) (6 states, 8 symbols)
    Previous best dominated bounds: BB(6, 7) > f_{ω×2+1}(6), BB(4, 8) > f_{ω+4}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+2}(11)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwm2

namespace BB
namespace BB6_8

/-- The 6-state, 8-symbol Turing machine `bb68`:
    5RE3LB7LF2RA4LB6LF1RZ5RF_5LE3RB1LD2RA3LF7RC3LB3RA_3RB1LB3LC2RC4LC0LE6LE5LF_3RB6RD3LC2RC5LA3RE2LE1LB_5RC3RE2RA4LC6RA5LA2LE3RE_5RB7RD1LF1LF5RA5RF5LE0RD -/
def bb68 : TM
  -- State A (0): 5RE 3LB 7LF 2RA 4LB 6LF 1RZ 5RF
  | 0, 0 => some ⟨5, Dir.R, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨7, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.L, some 5⟩
  | 0, 6 => some ⟨1, Dir.R, none⟩
  | 0, 7 => some ⟨5, Dir.R, some 5⟩
  -- State B (1): 5LE 3RB 1LD 2RA 3LF 7RC 3LB 3RA
  | 1, 0 => some ⟨5, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨7, Dir.R, some 2⟩
  | 1, 6 => some ⟨3, Dir.L, some 1⟩
  | 1, 7 => some ⟨3, Dir.R, some 0⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 0LE 6LE 5LF
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  | 2, 6 => some ⟨6, Dir.L, some 4⟩
  | 2, 7 => some ⟨5, Dir.L, some 5⟩
  -- State D (3): 3RB 6RD 3LC 2RC 5LA 3RE 2LE 1LB
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨6, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨5, Dir.L, some 0⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  | 3, 6 => some ⟨2, Dir.L, some 4⟩
  | 3, 7 => some ⟨1, Dir.L, some 1⟩
  -- State E (4): 5RC 3RE 2RA 4LC 6RA 5LA 2LE 3RE
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨6, Dir.R, some 0⟩
  | 4, 5 => some ⟨5, Dir.L, some 0⟩
  | 4, 6 => some ⟨2, Dir.L, some 4⟩
  | 4, 7 => some ⟨3, Dir.R, some 4⟩
  -- State F (5): 5RB 7RD 1LF 1LF 5RA 5RF 5LE 0RD
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨7, Dir.R, some 3⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.R, some 0⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 4⟩
  | 5, 7 => some ⟨0, Dir.R, some 3⟩
  | _, _ => none

theorem bb68_valid : ValidTM 6 8 bb68 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 => simp [bb68]
    | _ + 6, _ => omega
    | _, _ + 8 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 => omega
    | _ + 6, _ => rfl
    | 0, _ + 8 | 1, _ + 8 | 2, _ + 8 | 3, _ + 8 | 4, _ + 8 | 5, _ + 8 => rfl

theorem bb68_fwm2 : Fwm2Core bb68 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem rep_add (a b s : Nat) (R : List Nat) :
    rep a s (rep b s R) = rep (a + b) s R := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

private theorem loop_F2 (n : Nat) (L R : List Nat) :
    Reaches bb68 (mkCfgR (some 5) (rep n 2 L) (2 :: R))
                 (mkCfgR (some 5) L (2 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb68 _
  | succ k ih =>
    have h1 : step bb68 (mkCfgR (some 5) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 5) (rep k 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb68) (q := 5) (w := 0) (cur := 2) rfl
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb68 k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb68 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb68 _
  | succ k ih =>
    have h1 : step bb68 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb68) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb68 k _ _ _ h1 h2

private theorem loop_D1 (n : Nat) (L R : List Nat) :
    Reaches bb68 (mkCfgR (some 3) L (rep n 1 R))
                 (mkCfgR (some 3) (rep n 6 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb68 _
  | succ k ih =>
    have h1 : step bb68 (mkCfgR (some 3) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 3) (6 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb68) (q := 3) (w := 5) (cur := 1) rfl
    have h2 := ih (6 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ bb68 k _ _ _ h1 h2

private theorem loop_B6 (n : Nat) (L R : List Nat) :
    Reaches bb68 (mkCfgR (some 1) (rep n 6 L) (6 :: R))
                 (mkCfgR (some 1) L (6 :: rep n 3 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb68 _
  | succ k ih =>
    have h1 : step bb68 (mkCfgR (some 1) (6 :: rep k 6 L) (6 :: R)) =
              some (mkCfgR (some 1) (rep k 6 L) (6 :: 3 :: R)) :=
      step_mkCfgR_L_cons (tm := bb68) (q := 1) (w := 2) (cur := 6) rfl
    have h2 := ih (3 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb68 k _ _ _ h1 h2

private theorem loop_E6 (n : Nat) (L R : List Nat) :
    Reaches bb68 (mkCfgR (some 4) (rep n 6 L) (6 :: R))
                 (mkCfgR (some 4) L (6 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb68 _
  | succ k ih =>
    have h1 : step bb68 (mkCfgR (some 4) (6 :: rep k 6 L) (6 :: R)) =
              some (mkCfgR (some 4) (rep k 6 L) (6 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb68) (q := 4) (w := 1) (cur := 6) rfl
    have h2 := ih (2 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb68 k _ _ _ h1 h2

/-- Common first half of reload (`F` sweeps left converting `3,2 -> 1`, `D` sweeps right writing `7 6^(2m+k+1)`). -/
private theorem sweep_FD (k m mark : Nat) (R : List Nat) :
    ∃ t, Reaches bb68
      (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: mark :: R))
      (mkCfgR (some 3) (rep (2 * m + k + 1) 6 [7, 5]) (mark :: R)) t := by
  have h2 := loop_F2 k (rep (2 * m + 1) 3 [5]) (mark :: R)
  have h3 : step bb68 (mkCfgR (some 5) (3 :: rep (2 * m) 3 [5]) (2 :: rep k 1 (mark :: R))) =
            some (mkCfgR (some 5) (rep (2 * m) 3 [5]) (3 :: rep (k + 1) 1 (mark :: R))) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 5) (w := 0) (cur := 2) rfl
  have h4 := loop_F3 (2 * m) [5] (rep (k + 1) 1 (mark :: R))
  rw [rep_add] at h4
  have hrep1 : 2 * m + (k + 1) = 2 * m + k + 1 := by omega
  rw [hrep1] at h4
  have h5 : step bb68 (mkCfgR (some 5) [5] (3 :: rep (2 * m + k + 1) 1 (mark :: R))) =
            some (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (mark :: R))) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 5) (w := 0) (cur := 3) rfl
  have h6 : step bb68 (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (mark :: R))) =
            some (mkCfgR (some 5) [5] (rep (2 * m + k + 2) 1 (mark :: R))) :=
    step_mkCfgR_R (tm := bb68) (q := 5) (w := 4) (cur := 5) rfl
  have h7 : step bb68 (mkCfgR (some 5) [5] (1 :: rep (2 * m + k + 1) 1 (mark :: R))) =
            some (mkCfgR (some 3) [7, 5] (rep (2 * m + k + 1) 1 (mark :: R))) :=
    step_mkCfgR_R (tm := bb68) (q := 5) (w := 6) (cur := 1) rfl
  have h8 := loop_D1 (2 * m + k + 1) [7, 5] (mark :: R)
  exact ⟨_, reaches_trans (reaches_trans h2 (steps_succ bb68 _ _ _ _ h3 h4))
    (steps_succ bb68 _ _ _ _ h5 (steps_succ bb68 _ _ _ _ h6 (steps_succ bb68 _ _ _ _ h7 h8)))⟩

theorem reload_2 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb68 (B5cfg k m (2 :: R)) (B5cfg (2 * m + k) 0 (1 :: R)) t := by
  have h1 : step bb68 (B5cfg k m (2 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 0) (w := 6) (cur := 2) rfl
  obtain ⟨ts, hs⟩ := sweep_FD k m 7 R
  have h9 : step bb68 (mkCfgR (some 3) (6 :: rep (2 * m + k) 6 [7, 5]) (7 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + k) 6 [7, 5]) (6 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 3) (w := 0) (cur := 7) rfl
  have h10 := loop_B6 (2 * m + k) [7, 5] (1 :: R)
  have h11 : step bb68 (mkCfgR (some 1) [7, 5] (6 :: rep (2 * m + k) 3 (1 :: R))) =
             some (mkCfgR (some 1) [5] (7 :: rep (2 * m + k + 1) 3 (1 :: R))) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 1) (w := 2) (cur := 6) rfl
  have h12 : step bb68 (mkCfgR (some 1) [5] (7 :: rep (2 * m + k + 1) 3 (1 :: R))) =
             some (mkCfgR (some 0) [3, 5] (rep (2 * m + k + 1) 3 (1 :: R))) :=
    step_mkCfgR_R (tm := bb68) (q := 1) (w := 2) (cur := 7) rfl
  have h13 := loop_A3 bb68_fwm2.kc (2 * m + k + 1) [3, 5] (1 :: R)
  exact ⟨_, steps_succ bb68 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb68 _ _ _ _ h9 (reaches_trans h10
      (steps_succ bb68 _ _ _ _ h11 (steps_succ bb68 _ _ _ _ h12 h13)))))⟩

theorem reload_5 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb68 (B5cfg k m (5 :: R)) (B5cfg 0 0 (rep (2 * m + k + 1) 2 R)) t := by
  have h1 : step bb68 (B5cfg k m (5 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 0) (w := 5) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_FD k m 6 R
  have h9 : step bb68 (mkCfgR (some 3) (6 :: rep (2 * m + k) 6 [7, 5]) (6 :: R)) =
            some (mkCfgR (some 4) (rep (2 * m + k) 6 [7, 5]) (6 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 3) (w := 1) (cur := 6) rfl
  have h10 := loop_E6 (2 * m + k) [7, 5] (2 :: R)
  rw [rep_snoc_one] at h10
  have h11 : step bb68 (mkCfgR (some 4) [7, 5] (6 :: rep (2 * m + k + 1) 2 R)) =
             some (mkCfgR (some 4) [5] (7 :: rep (2 * m + k + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb68) (q := 4) (w := 1) (cur := 6) rfl
  have h12 : step bb68 (mkCfgR (some 4) [5] (7 :: rep (2 * m + k + 2) 2 R)) =
             some (mkCfgR (some 4) [3, 5] (rep (2 * m + k + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb68) (q := 4) (w := 2) (cur := 7) rfl
  have h13 : step bb68 (mkCfgR (some 4) [3, 5] (2 :: rep (2 * m + k + 1) 2 R)) =
             some (B5cfg 0 0 (rep (2 * m + k + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb68) (q := 4) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb68 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb68 _ _ _ _ h9 (reaches_trans h10
      (steps_succ bb68 _ _ _ _ h11 (steps_succ bb68 _ _ _ _ h12 (steps_one bb68 _ _ h13))))))⟩

/-! ### Growth Functions `H2` (`> f_{ω×2}`) and `H5` (`> f_{ω×2+1}`) -/

def H2 (m : Nat) : Nat := Wfn (2 * m) 0
def H5 (m : Nat) : Nat := iter H2 (2 * m) 15

theorem H2_mono {x y : Nat} (hxy : x ≤ y) : H2 x ≤ H2 y := Wfn_mono_k (by omega) 0

theorem H2_inc (m : Nat) (_hm : 1 ≤ m) : m + 1 ≤ H2 m := by
  have h := Wfn_zero_ge (2 * m); unfold H2; omega

theorem H2_gt (m : Nat) (hm : 1 ≤ m) : f_omega_mul2 m < H2 m :=
  Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 m) (Wfn_mono_k (by omega) 0)

theorem H5_mono {x y : Nat} (hxy : x ≤ y) : H5 x ≤ H5 y :=
  iter_mono_steps H2 (fun z => by have := Wfn_zero_ge (2 * z); unfold H2; omega) (by omega) 15

theorem H5_gt (m : Nat) (hm : 1 ≤ m) : f_omega_mul2_plus 1 m < H5 m :=
  climb_double H2 f_omega_mul2 15 (by omega) (fun _ _ h => H2_mono h) H2_inc H2_gt
    (fOmegaMul_props 2 0) m hm

theorem rule_2 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb68 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧ H2 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 k m R
  obtain ⟨t2, h2, hle2⟩ := fwm2_step bb68_fwm2 (2 * m + k) 0 R
  exact ⟨2 * m + k, Wfn (2 * m + k) 0, t1 + t2, reaches_trans h1 h2,
    Wfn_mono_k (by omega) 0, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem rule_2_rep (n : Nat) :
    ∀ k m R, ∃ k' m' t, Reaches bb68 (B5cfg k m (rep n 2 R)) (B5cfg k' m' R) t ∧
      iter H2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro k m R; exact ⟨k, m, 0, reaches_zero bb68 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro k m R
    cases p with
    | zero =>
      obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_2 k m R
      exact ⟨k1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_2 k m (rep (p' + 1) 2 R)
      obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := ih k1 m1 R
      have hcomm : iter H2 (p' + 1) (H2 m) = iter H2 (p' + 2) m := (iter_add H2 (p' + 1) 1 m).symm
      have hmb : iter H2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H2 (fun _ _ h => H2_mono h) (p' + 1) hm1) hm2
      exact ⟨k2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_5 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb68 (B5cfg k m (5 :: R)) (B5cfg k' m' R) t ∧ H5 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5 k m R
  obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_2 0 0 (rep (2 * m + k) 2 R)
  have hm1_15 : 15 ≤ m1 := by have : H2 0 = 15 := rfl; omega
  cases hmk : 2 * m + k with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    have hH5 : H5 0 = 15 := rfl
    rw [hmk] at h0 h1
    exact ⟨k1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ r =>
    rw [hmk] at h0 h1
    obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := rule_2_rep (r + 1) k1 m1 R
    have hstep : iter H2 (2 * m) 15 ≤ iter H2 (r + 1) 15 :=
      iter_mono_steps H2 (fun z => by have := Wfn_zero_ge (2 * z); unfold H2; omega) (by omega) 15
    have harg : iter H2 (r + 1) 15 ≤ iter H2 (r + 1) m1 :=
      iter_mono_arg H2 (fun _ _ h => H2_mono h) (r + 1) hm1_15
    exact ⟨k2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans (Nat.le_trans hstep harg) hm2,
      Nat.le_trans (ht2 (Nat.succ_pos r)) (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ k m R, ∃ k' m' t, Reaches bb68 (B5cfg k m (rep n 5 R)) (B5cfg k' m' R) t ∧
      iter H5 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro k m R; exact ⟨k, m, 0, reaches_zero bb68 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro k m R
    cases p with
    | zero =>
      obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_5 k m R
      exact ⟨k1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_5 k m (rep (p' + 1) 5 R)
      obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := ih k1 m1 R
      have hcomm : iter H5 (p' + 1) (H5 m) = iter H5 (p' + 2) m := (iter_add H5 (p' + 1) 1 m).symm
      have hmb : iter H5 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H5 (fun _ _ h => H5_mono h) (p' + 1) hm1) hm2
      exact ⟨k2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

/-! ### Exact 210-Step Bootstrap & Main Theorem -/

set_option maxRecDepth 2000 in
theorem bb68_bootstrap :
    Reaches bb68 initConfig (B5cfg 0 0 (2 :: rep 11 5 [6])) 210 := rfl

theorem bb68_halts_gt_f_omega_mul2_plus_2_11 :
    ValidTM 6 8 bb68 ∧ ∃ t, HaltsIn bb68 initConfig t ∧ f_omega_mul2_plus 2 11 < t := by
  refine ⟨bb68_valid, ?_⟩
  have hboot := bb68_bootstrap
  obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_2 0 0 (rep 11 5 [6])
  have hm1_ge : 11 ≤ m1 := by have : H2 0 = 15 := rfl; omega
  obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep 11 k1 m1 [6]
  have hhalt : step bb68 (B5cfg k2 m2 [6]) =
               some (mkCfgR none (1 :: rep (k2 + 1) 2 (rep (2 * m2 + 1) 3 [5])) []) :=
    step_mkCfgR_R (tm := bb68) (q := 0) (w := 0) (cur := 6) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) (steps_one bb68 _ _ hhalt)
  have hlt1 : f_omega_mul2_plus 2 11 < iter H5 11 11 :=
    iter_strict_dom H5 (f_omega_mul2_plus 1) 1 H5_gt (fOmegaMul_props 2 1) 11 11 (by omega) (by omega)
  have hlt2 : iter H5 11 11 ≤ iter H5 11 m1 := iter_mono_arg H5 (fun _ _ h => H5_mono h) 11 hm1_ge
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, ?_⟩
  omega

#print axioms bb68_halts_gt_f_omega_mul2_plus_2_11

end BB6_8
end BB
