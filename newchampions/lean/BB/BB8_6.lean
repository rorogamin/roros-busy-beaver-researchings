/-
  BB/BB8_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 6):
    TM: 2LF3LB2LH2RA4LB4LH_1RH3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC1RZ3RD_5RB3RE4RG4LC3LG5LE_5RB5RE1RZ1LF5LF5LF_5LF4RG1LB1LG2LH5LG_1RA1RZ1LH1LH2LH5RG
    Domain: BB(8, 6) (8 states, 6 symbols)
    Previous wiki champion: BB(8, 6) > f_{ω^2+1}(f_ω(31)) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(4)
    (strictly beats previous BB(8, 6) by a full FGH ordinal level, and strictly < our BB(9, 6) & BB(8, 7))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_6

def bb86 : TM
  -- State A (0): 2LF 3LB 2LH 2RA 4LB 4LH
  | 0, 0 => some ⟨2, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.L, some 7⟩
  -- State B (1): 1RH 3RB 1LD 2RA 3LF 5RB
  | 1, 0 => some ⟨1, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  -- State D (3): 3RB 3RE 3LC 2RC 1RZ 3RD
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.R, none⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  -- State F (5): 5RB 5RE 1RZ 1LF 5LF 5LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 4⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  -- State G (6): 5LF 4RG 1LB 1LG 2LH 5LG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.L, some 7⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  -- State H (7): 1RA 1RZ 1LH 1LH 2LH 5RG
  | 7, 0 => some ⟨1, Dir.R, some 0⟩
  | 7, 1 => some ⟨1, Dir.R, none⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | _, _ => none

theorem bb86_valid : ValidTM 8 6 bb86 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 7 => match sym with | 0 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 1 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 8 => rfl

theorem bb86_core : Fwp2_HCore bb86 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb86 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb86 _
  | succ k ih =>
    have h1 : step bb86 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb86) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb86 k _ _ _ h1 h2

theorem rule_5 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb86 (Scfg (r + 1) 0 m (5 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb86 (Scfg (r + 1) 0 m (5 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 0) (w := 3) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb86_core r m 4 R
  have h2 : step bb86 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 6) (w := 1) (cur := 4) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb86 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb86) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb86 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb86) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb86_core r m hm R
  have hpre := steps_succ bb86 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb86 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb86 _ _ _ _ h4 (steps_one bb86 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb86 (Scfg (r + 1) 0 m (rep n 5 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb86 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_5 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 r m hm (rep (p' + 1) 5 R)
      have hm1p : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1p
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb86_bootstrap :
    Reaches bb86 initConfig (Scfg 1 0 1 (rep 5 5 [])) 41 := rfl

theorem bb86_halts_gt_f_omega2_plus_2_4 :
    ValidTM 8 6 bb86 ∧ ∃ t, HaltsIn bb86 initConfig t ∧ f_omega2_plus 2 4 < t := by
  refine ⟨bb86_valid, ?_⟩
  have hboot := bb86_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 0 1 (by omega) (rep 4 5 [])
  have hm1_4 : 4 ≤ m1 := Nat.le_trans (by omega : 4 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep 4 (r1 + 1) m1 [] (by omega)
  have hh1 : step bb86 (Scfg (r2 + 1) 0 m2 []) =
             some (mkCfgR (some 5) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 2]) := rfl
  have hh2 : step bb86 (mkCfgR (some 5) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 2]) =
             some (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2]) :=
    step_mkCfgR_R (tm := bb86) (q := 5) (w := 0) (cur := 2) rfl
  have hhalt : Reaches bb86 (Scfg (r2 + 1) 0 m2 [])
      (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2]) 2 :=
    steps_succ bb86 1 _ _ _ hh1 (steps_one bb86 _ _ hh2)
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 2 4 < iter H_plus2 4 4 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 4 4 (by omega) (by omega)
  have hlt2 : iter H_plus2 4 4 ≤ iter H_plus2 4 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 4 hm1_4
  have hlt_m2 : f_omega2_plus 2 4 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb86_halts_gt_f_omega2_plus_2_4

end BB8_6
end BB
