/-
  BB/BB8_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(8, 7):
    TM: 6LC3LB2LH2RA4LB6LH1RZ_5RA3RB1LD2RA3LF5RB0RH_3RB1LB3LC2RC4LC1LE4LH_3RB3RE3LC2RC5RF3RD1RZ_5RB3RE4RG4LC3LG5LE1RZ_5RB5RB1RZ1LF5LF5LF1RH_5LF4RG1LB1LG5LD5LG2LH_5LA0LH1LH1LH2LH5RG1RZ
    Domain: BB(8, 7) (8 states, 7 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{ω^2+1}(f_ω(31)), BB(7, 7) > f_{ω^2+1}(3)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(8)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H

namespace BB
namespace BB8_7

def bb87 : TM
  -- State A (0): 6LC 3LB 2LH 2RA 4LB 6LH 1RZ
  | 0, 0 => some ⟨6, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.L, some 7⟩
  | 0, 6 => some ⟨1, Dir.R, none⟩
  -- State B (1): 5RA 3RB 1LD 2RA 3LF 5RB 0RH
  | 1, 0 => some ⟨5, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨0, Dir.R, some 7⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 4LH
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨4, Dir.L, some 7⟩
  -- State D (3): 3RB 3RE 3LC 2RC 5RF 3RD 1RZ
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨5, Dir.R, some 5⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨1, Dir.R, none⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 1RZ
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨1, Dir.R, none⟩
  -- State F (5): 5RB 5RB 1RZ 1LF 5LF 5LF 1RH
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨1, Dir.R, some 7⟩
  -- State G (6): 5LF 4RG 1LB 1LG 5LD 5LG 2LH
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.L, some 3⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  -- State H (7): 5LA 0LH 1LH 1LH 2LH 5RG 1RZ
  | 7, 0 => some ⟨5, Dir.L, some 0⟩
  | 7, 1 => some ⟨0, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨1, Dir.R, none⟩
  | _, _ => none

theorem bb87_valid : ValidTM 8 7 bb87 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 8 => rfl

theorem bb87_core : Fwp2_HCore bb87 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_H4 (n : Nat) (L R : List Nat) :
    Reaches bb87 (mkCfgR (some 7) (rep n 4 L) (4 :: R))
                 (mkCfgR (some 7) L (4 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb87 _
  | succ k ih =>
    have h1 : step bb87 (mkCfgR (some 7) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 7) (rep k 4 L) (4 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb87) (q := 7) (w := 1) (cur := 4) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb87 k _ _ _ h1 h2

theorem rule_5 (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches bb87 (Scfg (r + 1) 0 m (5 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have h1 : step bb87 (Scfg (r + 1) 0 m (5 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 0) (w := 5) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb87_core r m 6 R
  have h2 : step bb87 (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (6 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 6) (w := 1) (cur := 6) rfl
  have h3 := loop_H4 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb87 (mkCfgR (some 7) (5 :: rep r 5 []) (4 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb87) (q := 7) (w := 1) (cur := 4) rfl
  have h5 : step bb87 (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 3) 2 R)) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R)) :=
    step_mkCfgR_R (tm := bb87) (q := 7) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he, hme, hte⟩ := exec_G2_2s bb87_core r m hm R
  have hpre := steps_succ bb87 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb87 _ _ _ _ h2 (reaches_trans h3 (steps_succ bb87 _ _ _ _ h4 (steps_one bb87 _ _ h5)))))
  exact ⟨r', m', _, reaches_trans hpre he, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ r m R, 1 ≤ m → ∃ r' m' t, Reaches bb87 (Scfg (r + 1) 0 m (rep n 5 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H_plus2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R _; exact ⟨r, m, 0, reaches_zero bb87 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R hm
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_5 r m hm R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 r m hm (rep (p' + 1) 5 R)
      have hm1_pos : 1 ≤ m1 := Nat.le_trans (by omega : 1 ≤ 17) (Nat.le_trans (H_plus2_ge_17 m) hm1)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R hm1_pos
      have hcomm : iter H_plus2 (p' + 1) (H_plus2 m) = iter H_plus2 (p' + 2) m :=
        (iter_add H_plus2 (p' + 1) 1 m).symm
      have hmb : iter H_plus2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb87_bootstrap :
    Reaches bb87 initConfig (Scfg 3 0 1 (rep 9 5 [1, 6])) 160 := rfl

theorem bb87_halts_gt_f_omega2_plus_2_8 :
    ValidTM 8 7 bb87 ∧ ∃ t, HaltsIn bb87 initConfig t ∧ f_omega2_plus 2 8 < t := by
  refine ⟨bb87_valid, ?_⟩
  have hboot := bb87_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5 2 1 (by omega) (rep 8 5 [1, 6])
  have hm1_8 : 8 ≤ m1 := Nat.le_trans (by omega : 8 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep 8 (r1 + 1) m1 [1, 6] (by omega)
  obtain ⟨t3, h3, _⟩ := fwp2_step bb87_core.fp (r2 + 1) 0 m2 [6]
  have hhalt : step bb87 (Scfg (r2 + 1) 0 (Pfn (r2 + 1) 0 m2) [6]) =
               some (mkCfgR none (1 :: 2 :: rep (2 * Pfn (r2 + 1) 0 m2 + 1) 3 (rep (r2 + 1) 5 [])) []) :=
    step_mkCfgR_R (tm := bb87) (q := 0) (w := 0) (cur := 6) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3)
    (steps_one bb87 _ _ hhalt)
  have hlt1 : f_omega2_plus 2 8 < iter H_plus2 8 8 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 8 8 (by omega) (by omega)
  have hlt2 : iter H_plus2 8 8 ≤ iter H_plus2 8 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 8 hm1_8
  have hlt_m2 : f_omega2_plus 2 8 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb87_halts_gt_f_omega2_plus_2_8

end BB8_7
end BB
