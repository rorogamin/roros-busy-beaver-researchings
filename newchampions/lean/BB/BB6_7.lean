/-
  BB/BB6_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(6, 7):
    TM: 6RD3LB6LF2RA4LB1RZ6LA_6LC3RB1LD2RA3LF4RE6LB_3RB1LB3LC2RC4LC0LE5LA_3RB2RD3LC2RC1LA3RE1LE_5RC3RE2RA4LC2LE2LE5RB_5RB3RD1LF1LF6LE5RF5LB
    Domain: BB(6, 7) (6 states, 7 symbols)
    Previous best dominated bounds: BB(5, 7) > f_{ω×2}(97), BB(6, 6) > f_{ω×2}(89)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+1}(6)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwm2

namespace BB
namespace BB6_7

/-- The 6-state, 7-symbol Turing machine `bb67`:
    6RD3LB6LF2RA4LB1RZ6LA_6LC3RB1LD2RA3LF4RE6LB_3RB1LB3LC2RC4LC0LE5LA_3RB2RD3LC2RC1LA3RE1LE_5RC3RE2RA4LC2LE2LE5RB_5RB3RD1LF1LF6LE5RF5LB -/
def bb67 : TM
  -- State A (0): 6RD 3LB 6LF 2RA 4LB 1RZ 6LA
  | 0, 0 => some ⟨6, Dir.R, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨6, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨1, Dir.R, none⟩
  | 0, 6 => some ⟨6, Dir.L, some 0⟩
  -- State B (1): 6LC 3RB 1LD 2RA 3LF 4RE 6LB
  | 1, 0 => some ⟨6, Dir.L, some 2⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨4, Dir.R, some 4⟩
  | 1, 6 => some ⟨6, Dir.L, some 1⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 0LE 5LA
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  | 2, 6 => some ⟨5, Dir.L, some 0⟩
  -- State D (3): 3RB 2RD 3LC 2RC 1LA 3RE 1LE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨2, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.L, some 0⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  | 3, 6 => some ⟨1, Dir.L, some 4⟩
  -- State E (4): 5RC 3RE 2RA 4LC 2LE 2LE 5RB
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨2, Dir.L, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 4⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  -- State F (5): 5RB 3RD 1LF 1LF 6LE 5RF 5LB
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨3, Dir.R, some 3⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨6, Dir.L, some 4⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 1⟩
  | _, _ => none

theorem bb67_valid : ValidTM 6 7 bb67 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 => simp [bb67]
    | _ + 6, _ => omega
    | _, _ + 7 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 => omega
    | _ + 6, _ => rfl
    | 0, _ + 7 | 1, _ + 7 | 2, _ + 7 | 3, _ + 7 | 4, _ + 7 | 5, _ + 7 => rfl

theorem bb67_fwm2 : Fwm2Core bb67 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Reload Loops for Symbol `2` -/

private theorem loop_F2 (n : Nat) (L R : List Nat) :
    Reaches bb67 (mkCfgR (some 5) (rep n 2 L) (2 :: R))
                 (mkCfgR (some 5) L (2 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb67 _
  | succ k ih =>
    have h1 : step bb67 (mkCfgR (some 5) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 5) (rep k 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb67) (q := 5) (w := 0) (cur := 2) rfl
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb67 k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb67 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb67 _
  | succ k ih =>
    have h1 : step bb67 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb67) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb67 k _ _ _ h1 h2

private theorem loop_D1 (n : Nat) (L R : List Nat) :
    Reaches bb67 (mkCfgR (some 3) L (rep n 1 R))
                 (mkCfgR (some 3) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb67 _
  | succ k ih =>
    have h1 : step bb67 (mkCfgR (some 3) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 3) (2 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb67) (q := 3) (w := 1) (cur := 1) rfl
    have h2 := ih (2 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ bb67 k _ _ _ h1 h2

private theorem rep_add (a b s : Nat) (R : List Nat) :
    rep a s (rep b s R) = rep (a + b) s R := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem reload_2 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb67 (B5cfg k m (2 :: R)) (B5cfg (2 * m + k) 0 (1 :: R)) t := by
  have h1 : step bb67 (B5cfg k m (2 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb67) (q := 0) (w := 5) (cur := 2) rfl
  have h2 := loop_F2 k (rep (2 * m + 1) 3 [5]) (6 :: R)
  have h3 : step bb67 (mkCfgR (some 5) (3 :: rep (2 * m) 3 [5]) (2 :: rep k 1 (6 :: R))) =
            some (mkCfgR (some 5) (rep (2 * m) 3 [5]) (3 :: rep (k + 1) 1 (6 :: R))) :=
    step_mkCfgR_L_cons (tm := bb67) (q := 5) (w := 0) (cur := 2) rfl
  have h4 := loop_F3 (2 * m) [5] (rep (k + 1) 1 (6 :: R))
  rw [rep_add] at h4
  have hrep1 : 2 * m + (k + 1) = 2 * m + k + 1 := by omega
  rw [hrep1] at h4
  have h5 : step bb67 (mkCfgR (some 5) [5] (3 :: rep (2 * m + k + 1) 1 (6 :: R))) =
            some (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (6 :: R))) :=
    step_mkCfgR_L_cons (tm := bb67) (q := 5) (w := 0) (cur := 3) rfl
  have h6 : step bb67 (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (6 :: R))) =
            some (mkCfgR (some 5) [5] (rep (2 * m + k + 2) 1 (6 :: R))) :=
    step_mkCfgR_R (tm := bb67) (q := 5) (w := 4) (cur := 5) rfl
  have h7 : step bb67 (mkCfgR (some 5) [5] (1 :: rep (2 * m + k + 1) 1 (6 :: R))) =
            some (mkCfgR (some 3) [3, 5] (rep (2 * m + k + 1) 1 (6 :: R))) :=
    step_mkCfgR_R (tm := bb67) (q := 5) (w := 2) (cur := 1) rfl
  have h8 := loop_D1 (2 * m + k + 1) [3, 5] (6 :: R)
  have h9 : step bb67 (mkCfgR (some 3) (2 :: rep (2 * m + k) 2 [3, 5]) (6 :: R)) =
            some (mkCfgR (some 4) (rep (2 * m + k) 2 [3, 5]) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb67) (q := 3) (w := 0) (cur := 6) rfl
  have h10 : step bb67 (mkCfgR (some 4) (rep (2 * m + k) 2 [3, 5]) (2 :: 1 :: R)) =
             some (B5cfg (2 * m + k) 0 (1 :: R)) :=
    step_mkCfgR_R (tm := bb67) (q := 4) (w := 1) (cur := 2) rfl
  have ha := steps_succ bb67 _ _ _ _ h1 (reaches_trans h2 (steps_succ bb67 _ _ _ _ h3 h4))
  have hb := steps_succ bb67 _ _ _ _ h5 (steps_succ bb67 _ _ _ _ h6
    (steps_succ bb67 _ _ _ _ h7 (reaches_trans h8 (steps_succ bb67 _ _ _ _ h9 (steps_one bb67 _ _ h10)))))
  exact ⟨_, reaches_trans ha hb⟩

/-- Combined Rule 2: `B5cfg k m (2 :: R) --> B5cfg (2*m + k) (Wfn (2*m + k) 0) R` with `Wfn (2*m) 0 ≤ t`. -/
def H2 (m : Nat) : Nat := Wfn (2 * m) 0

theorem rule_2 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb67 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧ H2 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 k m R
  obtain ⟨t2, h2, hle2⟩ := fwm2_step bb67_fwm2 (2 * m + k) 0 R
  have hmono : H2 m ≤ Wfn (2 * m + k) 0 := Wfn_mono_k (by omega : 2 * m ≤ 2 * m + k) 0
  exact ⟨2 * m + k, Wfn (2 * m + k) 0, t1 + t2, reaches_trans h1 h2, hmono, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem H2_mono {x y : Nat} (hxy : x ≤ y) : H2 x ≤ H2 y :=
  Wfn_mono_k (by omega) 0

theorem H2_gt_f_omega_mul2 (m : Nat) (hm : 1 ≤ m) : f_omega_mul2 m < H2 m := by
  have h1 := Wfn_succ_zero_gt_f_omega_mul2 m
  have h2 : Wfn (m + 1) 0 ≤ Wfn (2 * m) 0 := Wfn_mono_k (by omega) 0
  exact Nat.lt_of_lt_of_le h1 h2

theorem rule_2_rep (n : Nat) :
    ∀ k m R, ∃ k' m' t, Reaches bb67 (B5cfg k m (rep n 2 R)) (B5cfg k' m' R) t ∧
      iter H2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero =>
    intro k m R
    exact ⟨k, m, 0, reaches_zero bb67 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro k m R
    cases p with
    | zero =>
      obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_2 k m R
      exact ⟨k1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_2 k m (rep (p' + 1) 2 R)
      obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := ih k1 m1 R
      have hcomm : iter H2 (p' + 1) (H2 m) = iter H2 (p' + 2) m := by
        have h := iter_add H2 (p' + 1) 1 m; exact h.symm
      have hm_bound : iter H2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]
        exact Nat.le_trans (iter_mono_arg H2 (fun _ _ h => H2_mono h) (p' + 1) hm1) hm2
      exact ⟨k2, m2, t1 + t2, reaches_trans h1 h2, hm_bound, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

/-! ### Exact 46-Step Bootstrap & Main Theorem -/

theorem bb67_bootstrap :
    Reaches bb67 initConfig (B5cfg 0 0 [2, 2, 2, 2, 2, 2, 2, 5]) 46 := rfl

theorem bb67_halts_gt_f_omega_mul2_plus_1_6 :
    ValidTM 6 7 bb67 ∧ ∃ t, HaltsIn bb67 initConfig t ∧ f_omega_mul2_plus 1 6 < t := by
  refine ⟨bb67_valid, ?_⟩
  have hboot := bb67_bootstrap
  obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_2 0 0 [2, 2, 2, 2, 2, 2, 5]
  have hm1_ge : 6 ≤ m1 := by
    have h15 : H2 0 = 15 := rfl
    omega
  obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := rule_2_rep 6 k1 m1 [5]
  have hhalt : step bb67 (B5cfg k2 m2 [5]) =
               some (mkCfgR none (1 :: rep (k2 + 1) 2 (rep (2 * m2 + 1) 3 [5])) []) :=
    step_mkCfgR_R (tm := bb67) (q := 0) (w := 0) (cur := 5) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) (steps_one bb67 _ _ hhalt)
  have hlt1 : f_omega_mul2_plus 1 6 < iter H2 6 6 :=
    iter_strict_dom H2 f_omega_mul2 1 H2_gt_f_omega_mul2 (fOmegaMul_props 2 0) 6 6 (by omega) (by omega)
  have hlt2 : iter H2 6 6 ≤ iter H2 6 m1 := iter_mono_arg H2 (fun _ _ h => H2_mono h) 6 hm1_ge
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, ?_⟩
  omega

#print axioms bb67_halts_gt_f_omega_mul2_plus_1_6

end BB6_7
end BB
