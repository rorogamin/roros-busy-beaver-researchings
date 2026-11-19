/-
  BB/BB9_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(9, 6):
    TM: 4LH3LB2LH2RA4LB2RI_4LA3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC5LC3RD_5RB3RE4RG4LC3LG5LE_5RB5RB1RH1LF5LF5LF_5LF4RG1LB1LG2RG5LG_1LC1RD1LH1LH5RC5RG_1RZ5LI2LI2LI1LB5RG
    Domain: BB(9, 6) (9 states, 6 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{ω^2+1}(f_ω(31)), BB(9, 5) > f_{ω^2+1}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB9_6

def bb96 : TM
  -- State A (0): 4LH 3LB 2LH 2RA 4LB 2RI
  | 0, 0 => some ⟨4, Dir.L, some 7⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.R, some 8⟩
  -- State B (1): 4LA 3RB 1LD 2RA 3LF 5RB
  | 1, 0 => some ⟨4, Dir.L, some 0⟩
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
  -- State D (3): 3RB 3RE 3LC 2RC 5LC 3RD
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨5, Dir.L, some 2⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  -- State F (5): 5RB 5RB 1RH 1LF 5LF 5LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨1, Dir.R, some 7⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  -- State G (6): 5LF 4RG 1LB 1LG 2RG 5LG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 6⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  -- State H (7): 1LC 1RD 1LH 1LH 5RC 5RG
  | 7, 0 => some ⟨1, Dir.L, some 2⟩
  | 7, 1 => some ⟨1, Dir.R, some 3⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨5, Dir.R, some 2⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  -- State I (8): 1RZ 5LI 2LI 2LI 1LB 5RG
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 8⟩
  | 8, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 1⟩
  | 8, 5 => some ⟨5, Dir.R, some 6⟩
  | _, _ => none

theorem bb96_valid : ValidTM 9 6 bb96 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | _ + 9 => omega
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
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 9 => rfl

theorem bb96_core : Fwp2_HCore bb96 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have ha : step bb96 (Scfg (r + 1) 0 m (5 :: 1 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
    step_mkCfgR_R (tm := bb96) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb96 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
            some (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 4) (cur := 1) rfl
  have hc : step bb96 (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 2) rfl
  have hd : step bb96 (mkCfgR (some 8) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 2) rfl
  have he := loop_L3 (tm := bb96) (q := 8) (w' := 1) rfl (2 * m) (rep (r + 1) 5 []) (2 :: 2 :: 5 :: R)
  rw [rep_snoc_one, rep_snoc_one] at he
  have hf : step bb96 (mkCfgR (some 8) (5 :: rep r 5 []) (3 :: rep (2 * m + 2) 2 (5 :: R))) =
            some (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_L_cons (tm := bb96) (q := 8) (w := 1) (cur := 3) rfl
  have hg : step bb96 (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_R (tm := bb96) (q := 8) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he2, hme, hte⟩ := exec_G2_2s bb96_core r m hm (5 :: R)
  have hpre := reaches_trans
    (steps_succ bb96 _ _ _ _ ha (steps_succ bb96 _ _ _ _ hb
      (steps_succ bb96 _ _ _ _ hc (steps_succ bb96 _ _ _ _ hd he))))
    (steps_succ bb96 _ _ _ _ hf (steps_one bb96 _ _ hg))
  exact ⟨r' + 1, m', _, reaches_trans hpre he2, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb96_bootstrap :
    Reaches bb96 initConfig (Scfg 3 0 1 (5 :: rep 8 1 [])) 112 := rfl

theorem bb96_halts_gt_f_omega2_plus_2_7 :
    ValidTM 9 6 bb96 ∧ ∃ t, HaltsIn bb96 initConfig t ∧ f_omega2_plus 2 7 < t := by
  refine ⟨bb96_valid, ?_⟩
  have hboot := bb96_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 2 1 (rep 7 1 []) (by omega)
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H_plus2_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 1 H_plus2
    (fun _ _ h => H_plus2_mono h) (fun z _ => Nat.le_trans (by omega : 1 ≤ 17) (H_plus2_ge_17 z))
    rule_51 7 r1 m1 [] (by omega)
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb96) (mark' := 1) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 2 7 < iter H_plus2 7 7 :=
    iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 7 7 (by omega) (by omega)
  have hlt2 : iter H_plus2 7 7 ≤ iter H_plus2 7 m1 := iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 2 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb96_halts_gt_f_omega2_plus_2_7

end BB9_6
end BB
