/-
  BB/BB6_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(6, 6):
    TM: 5RE3LB4LF2RA4LB1RZ_5LE3RB1LD2RA3LF3RD_3RB1LB3LC2RC4LC0LE_3RB2RD3LC2RC1LE3RE_5RC3RE2RA4LC2LE2LA_5RB1RZ1LF1LF1RF5LF
    Domain: BB(6, 6) (6 states, 6 symbols)
    Previous wiki champion: BB(6, 6) > f_{ω×2}(89) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+1}(2)
    (strictly beats f_{ω×2}(89) by a full FGH ordinal level, and strictly < our BB(6, 7) & BB(7, 6))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwm2

namespace BB
namespace BB6_6

def bb66 : TM
  -- State A (0): 5RE 3LB 4LF 2RA 4LB 1RZ
  | 0, 0 => some ⟨5, Dir.R, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨1, Dir.R, none⟩
  -- State B (1): 5LE 3RB 1LD 2RA 3LF 3RD
  | 1, 0 => some ⟨5, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨3, Dir.R, some 3⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 0LE
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  -- State D (3): 3RB 2RD 3LC 2RC 1LE 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨2, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.L, some 4⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  -- State E (4): 5RC 3RE 2RA 4LC 2LE 2LA
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨2, Dir.L, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 0⟩
  -- State F (5): 5RB 1RZ 1LF 1LF 1RF 5LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, none⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨1, Dir.R, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | _, _ => none

theorem bb66_valid : ValidTM 6 6 bb66 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 1 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 6 => rfl

theorem bb66_core : Fwm2Core bb66 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_F2 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 5) (rep n 2 L) (2 :: R))
                 (mkCfgR (some 5) L (2 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 5) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 5) (rep k 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 2) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem loop_D1 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 3) L (rep n 1 R))
                 (mkCfgR (some 3) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 3) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 3) (2 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb66) (q := 3) (w := 1) (cur := 1) rfl
    have h2 := ih (2 :: L); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem rep_add (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem reload_2 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg (k + 2 * m + 1) 0 (1 :: R)) t := by
  have h1 : step bb66 (B5cfg k m (2 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 0) (w := 3) (cur := 2) rfl
  have h2 := loop_F2 k (rep (2 * m + 1) 3 [5]) (4 :: R)
  have h3 : step bb66 (mkCfgR (some 5) (3 :: rep (2 * m) 3 [5]) (2 :: rep k 1 (4 :: R))) =
            some (mkCfgR (some 5) (rep (2 * m) 3 [5]) (3 :: rep (k + 1) 1 (4 :: R))) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 2) rfl
  have h4 := loop_F3 (2 * m) [5] (rep (k + 1) 1 (4 :: R))
  rw [rep_add] at h4
  have h5 : step bb66 (mkCfgR (some 5) [5] (3 :: rep (2 * m + (k + 1)) 1 (4 :: R))) =
            some (mkCfgR (some 5) [] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) := by
    have heq : (2 * m + (k + 1)) + 1 = k + 2 * m + 2 := by omega
    rw [← heq]; exact step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 3) rfl
  have h6 : step bb66 (mkCfgR (some 5) [] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 5) [] (0 :: 5 :: rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_L_nil (tm := bb66) (q := 5) (w := 4) (cur := 5) rfl
  have h7 : step bb66 (mkCfgR (some 5) [] (0 :: 5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 1) [5] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_R (tm := bb66) (q := 5) (w := 4) (cur := 0) rfl
  have h8 : step bb66 (mkCfgR (some 1) [5] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 3) [3, 5] (rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_R (tm := bb66) (q := 1) (w := 2) (cur := 5) rfl
  have h9 := loop_D1 (k + 2 * m + 2) [3, 5] (4 :: R)
  have h10 : step bb66 (mkCfgR (some 3) (2 :: rep (k + 2 * m + 1) 2 [3, 5]) (4 :: R)) =
             some (mkCfgR (some 4) (rep (k + 2 * m + 1) 2 [3, 5]) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 3) (w := 0) (cur := 4) rfl
  have h11 : step bb66 (mkCfgR (some 4) (rep (k + 2 * m + 1) 2 [3, 5]) (2 :: 1 :: R)) =
             some (B5cfg (k + 2 * m + 1) 0 (1 :: R)) :=
    step_mkCfgR_R (tm := bb66) (q := 4) (w := 1) (cur := 2) rfl
  exact ⟨_, reaches_trans
    (steps_succ bb66 _ _ _ _ h1 (reaches_trans h2 (steps_succ bb66 _ _ _ _ h3 h4)))
    (steps_succ bb66 _ _ _ _ h5 (steps_succ bb66 _ _ _ _ h6 (steps_succ bb66 _ _ _ _ h7
      (steps_succ bb66 _ _ _ _ h8 (reaches_trans h9 (steps_succ bb66 _ _ _ _ h10 (steps_one bb66 _ _ h11)))))))⟩

theorem rule_2 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧
      Wfn (2 * m + 1) 0 ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 k m R
  obtain ⟨t2, h2, hle2⟩ := fwm2_step bb66_core (k + 2 * m + 1) 0 R
  exact ⟨k + 2 * m + 1, Wfn (k + 2 * m + 1) 0, t1 + t2, reaches_trans h1 h2,
    Wfn_mono_k (by omega) 0, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem bb66_bootstrap :
    Reaches bb66 initConfig (B5cfg 0 0 [1, 1, 1, 2, 2, 5]) 40 := rfl

theorem bb66_halts_gt_f_omega_mul2_plus_1_2 :
    ValidTM 6 6 bb66 ∧ ∃ t, HaltsIn bb66 initConfig t ∧ f_omega_mul2_plus 1 2 < t := by
  refine ⟨bb66_valid, ?_⟩
  have hboot := bb66_bootstrap
  obtain ⟨t1, h1, _⟩ := fwm2_step bb66_core 0 0 [1, 1, 2, 2, 5]
  obtain ⟨t2, h2, _⟩ := fwm2_step bb66_core 0 (Wfn 0 0) [1, 2, 2, 5]
  obtain ⟨t3, h3, _⟩ := fwm2_step bb66_core 0 (Wfn 0 (Wfn 0 0)) [2, 2, 5]
  have hm3_ge : 2 ≤ Wfn 0 (Wfn 0 (Wfn 0 0)) := by
    have a := Wfn_ge_succ 0 0
    have b := Wfn_ge_succ 0 (Wfn 0 0)
    have c := Wfn_ge_succ 0 (Wfn 0 (Wfn 0 0))
    omega
  obtain ⟨k4, m4, t4, h4, hm4, _⟩ := rule_2 0 (Wfn 0 (Wfn 0 (Wfn 0 0))) [2, 5]
  obtain ⟨k5, m5, t5, h5, hm5, ht5⟩ := rule_2 k4 m4 [5]
  have hhalt : step bb66 (B5cfg k5 m5 [5]) =
               some (mkCfgR none (1 :: rep (k5 + 1) 2 (rep (2 * m5 + 1) 3 [5])) []) :=
    step_mkCfgR_R (tm := bb66) (q := 0) (w := 0) (cur := 5) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans (reaches_trans hboot h1) h2) h3) h4) h5) (steps_one bb66 _ _ hhalt)
  have hlt1 : f_omega_mul2 2 < m4 :=
    Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 2)
      (Nat.le_trans (Wfn_mono_k (by omega : 3 ≤ 2 * Wfn 0 (Wfn 0 (Wfn 0 0)) + 1) 0) hm4)
  have hlt2 : f_omega_mul2 (f_omega_mul2 2) ≤ f_omega_mul2 m4 :=
    (fOmegaMul_props 2 0).mono _ _ (Nat.le_of_lt hlt1)
  have hlt3 : f_omega_mul2 m4 < m5 :=
    Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 m4)
      (Nat.le_trans (Wfn_mono_k (by omega : m4 + 1 ≤ 2 * m4 + 1) 0) hm5)
  have hdef : f_omega_mul2_plus 1 2 = f_omega_mul2 (f_omega_mul2 2) := by
    change iter f_omega_mul2 2 2 = f_omega_mul2 (f_omega_mul2 2)
    rw [iter_succ, iter_succ, iter_zero]
  have hlt_m5 : f_omega_mul2_plus 1 2 < m5 := by rw [hdef]; exact Nat.lt_of_le_of_lt hlt2 hlt3
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m5 (Nat.le_trans ht5 (by omega))⟩

#print axioms bb66_halts_gt_f_omega_mul2_plus_1_2

end BB6_6
end BB
