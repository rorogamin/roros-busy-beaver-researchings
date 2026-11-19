/-
  BB/BB10_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(10, 6):
    TM: 1LJ3LB2LH2RA4LB2RI_1LA3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC2RF3RD_5RB3RE4RG4LC3LG5LE_5RB5RB1LA1LF5LF5LF_5LF4RG1LB1LG4LJ5LG_1RJ3LD1LH1LH3RD5RG_1RZ4LH2LI2LI5LI5RG_1RD1RI0LB3RB4LJ5RH
    Domain: BB(10, 6) (10 states, 6 symbols)
    Previous best dominated bounds: BB(9, 6) > f_{ω^2+2}(7), BB(10, 5) > f_{ω^2+2}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB10_6

def bb106 : TM
  -- State A (0): 1LJ 3LB 2LH 2RA 4LB 2RI
  | 0, 0 => some ⟨1, Dir.L, some 9⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.R, some 8⟩
  -- State B (1): 1LA 3RB 1LD 2RA 3LF 5RB
  | 1, 0 => some ⟨1, Dir.L, some 0⟩
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
  -- State D (3): 3RB 3RE 3LC 2RC 2RF 3RD
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨2, Dir.R, some 5⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  -- State F (5): 5RB 5RB 1LA 1LF 5LF 5LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨1, Dir.L, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  -- State G (6): 5LF 4RG 1LB 1LG 4LJ 5LG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨4, Dir.L, some 9⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  -- State H (7): 1RJ 3LD 1LH 1LH 3RD 5RG
  | 7, 0 => some ⟨1, Dir.R, some 9⟩
  | 7, 1 => some ⟨3, Dir.L, some 3⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨3, Dir.R, some 3⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  -- State I (8): 1RZ 4LH 2LI 2LI 5LI 5RG
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨4, Dir.L, some 7⟩
  | 8, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨5, Dir.L, some 8⟩
  | 8, 5 => some ⟨5, Dir.R, some 6⟩
  -- State J (9): 1RD 1RI 0LB 3RB 4LJ 5RH
  | 9, 0 => some ⟨1, Dir.R, some 3⟩
  | 9, 1 => some ⟨1, Dir.R, some 8⟩
  | 9, 2 => some ⟨0, Dir.L, some 1⟩
  | 9, 3 => some ⟨3, Dir.R, some 1⟩
  | 9, 4 => some ⟨4, Dir.L, some 9⟩
  | 9, 5 => some ⟨5, Dir.R, some 7⟩
  | _, _ => none

theorem bb106_valid : ValidTM 10 6 bb106 := by
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
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | _ + 10 => omega
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
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 10 => rfl

theorem bb106_core : Fwp2_HCore bb106 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_J4 (n : Nat) (L R : List Nat) :
    Reaches bb106 (mkCfgR (some 9) (rep n 4 L) (4 :: R))
                  (mkCfgR (some 9) L (4 :: rep n 4 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb106 _
  | succ k ih =>
    have h1 : step bb106 (mkCfgR (some 9) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 9) (rep k 4 L) (4 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb106) (q := 9) (w := 3) (cur := 4) rfl
    have h2 := ih (4 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb106 k _ _ _ h1 h2

theorem rule_54 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H_plus2 m ≤ m' ∧ m' ≤ t := by
  have ha : step bb106 (Scfg (r + 1) 0 m (5 :: 4 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb106 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 4) (cur := 4) rfl
  have hc : step bb106 (mkCfgR (some 8) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 2) rfl
  have hd : step bb106 (mkCfgR (some 8) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: 5 :: R)) =
            some (mkCfgR (some 8) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 2 :: 2 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 2) rfl
  have he := loop_L3 (tm := bb106) (q := 8) (w' := 1) rfl (2 * m) (rep (r + 1) 5 []) (2 :: 2 :: 5 :: R)
  rw [rep_snoc_one, rep_snoc_one] at he
  have hf : step bb106 (mkCfgR (some 8) (5 :: rep r 5 []) (3 :: rep (2 * m + 2) 2 (5 :: R))) =
            some (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 1) (cur := 3) rfl
  have hg : step bb106 (mkCfgR (some 8) (rep r 5 []) (5 :: rep (2 * m + 3) 2 (5 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 (5 :: R))) :=
    step_mkCfgR_R (tm := bb106) (q := 8) (w := 4) (cur := 5) rfl
  obtain ⟨r', m', te, he2, hme, hte⟩ := exec_G2_2s bb106_core r m hm (5 :: R)
  have hpre := reaches_trans
    (steps_succ bb106 _ _ _ _ ha (steps_succ bb106 _ _ _ _ hb
      (steps_succ bb106 _ _ _ _ hc (steps_succ bb106 _ _ _ _ hd he))))
    (steps_succ bb106 _ _ _ _ hf (steps_one bb106 _ _ hg))
  exact ⟨r' + 1, m', _, reaches_trans hpre he2, hme, Nat.le_trans hte (Nat.le_add_left _ _)⟩

def H51 (m : Nat) : Nat := iter H_plus2 (2 * m + 1) 1

theorem H51_mono {x y : Nat} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H51 m :=
  climb_2m_plus_1 H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H51_ge_17 (m : Nat) : 17 ≤ H51 m :=
  iter_H_ge_17 H_plus2 (2 * m + 1) 1 (by omega) (by omega) H_plus2_inc (fun z _ => H_plus2_ge_17 z)

theorem reload_51 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R))
                       (Scfg (r + 1) 0 (Pempty r) (5 :: rep (2 * m + 1) 4 R)) t := by
  have ha : step bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) =
            some (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 5) rfl
  have hb : step bb106 (mkCfgR (some 8) (2 :: 2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (1 :: R)) =
            some (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 8) (w := 3) (cur := 1) rfl
  have hc : step bb106 (mkCfgR (some 7) (2 :: rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 4 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 1 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 7) (w := 0) (cur := 2) rfl
  obtain ⟨ts, hs⟩ := sweep_HG bb106_core r m 1 (4 :: R)
  have hd : step bb106 (mkCfgR (some 6) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (1 :: 4 :: R)) =
            some (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) :=
    step_mkCfgR_R (tm := bb106) (q := 6) (w := 3) (cur := 1) rfl
  have he : step bb106 (mkCfgR (some 6) (4 :: rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: R)) =
            some (mkCfgR (some 9) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (4 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 6) (w := 3) (cur := 4) rfl
  have hf := loop_J4 (2 * m + 2) (rep (r + 1) 5 []) (4 :: R)
  rw [rep_snoc_one] at hf
  have hg : step bb106 (mkCfgR (some 9) (5 :: rep r 5 []) (4 :: rep (2 * m + 3) 4 R)) =
            some (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_L_cons (tm := bb106) (q := 9) (w := 3) (cur := 4) rfl
  have hh : step bb106 (mkCfgR (some 9) (rep r 5 []) (5 :: rep (2 * m + 4) 4 R)) =
            some (mkCfgR (some 7) (rep (r + 1) 5 []) (rep (2 * m + 4) 4 R)) :=
    step_mkCfgR_R (tm := bb106) (q := 9) (w := 4) (cur := 5) rfl
  have hsplit : rep (2 * m + 4) 4 R = 4 :: 4 :: 4 :: rep (2 * m + 1) 4 R := by
    have heq : 2 * m + 4 = (2 * m + 1) + 3 := by omega
    rw [heq]; rfl
  rw [hsplit] at hh
  have hi : Reaches bb106
      (mkCfgR (some 7) (rep (r + 1) 5 []) (4 :: 4 :: 4 :: rep (2 * m + 1) 4 R))
      (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: 5 :: rep (2 * m + 1) 4 R)) 5 := by
    refine steps_succ bb106 4 _ _ _ (step_mkCfgR_R (tm := bb106) (q := 7) (w := 2) (cur := 4) rfl) ?_
    refine steps_succ bb106 3 _ _ _ (step_mkCfgR_R (tm := bb106) (q := 3) (w := 1) (cur := 4) rfl) ?_
    refine steps_succ bb106 2 _ _ _ (step_mkCfgR_L_cons (tm := bb106) (q := 5) (w := 4) (cur := 4) rfl) ?_
    refine steps_succ bb106 1 _ _ _ (step_mkCfgR_L_cons (tm := bb106) (q := 5) (w := 0) (cur := 2) rfl) ?_
    exact steps_one bb106 _ _ (step_mkCfgR_R (tm := bb106) (q := 0) (w := 1) (cur := 3) rfl)
  obtain ⟨te, hempty, _⟩ := fwp2_empty3 bb106_core.fp r (5 :: rep (2 * m + 1) 4 R)
  have hp1 := steps_succ bb106 _ _ _ _ ha (steps_succ bb106 _ _ _ _ hb (steps_succ bb106 _ _ _ _ hc
    (reaches_trans hs (steps_succ bb106 _ _ _ _ hd (steps_succ bb106 _ _ _ _ he hf)))))
  have hp2 := steps_succ bb106 _ _ _ _ hg (steps_succ bb106 _ _ _ _ hh (reaches_trans hi hempty))
  exact ⟨_, reaches_trans hp1 hp2⟩

theorem rule_51 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb106 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51 r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega : 1 ≤ r + 2) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 4 H_plus2
    (fun _ _ h => H_plus2_mono h) (fun z _ => Nat.le_trans (by omega : 1 ≤ 17) (H_plus2_ge_17 z))
    rule_54 (2 * m + 1) r (Pempty r) R hpe
  have harg : H51 m ≤ iter H_plus2 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H_plus2 (fun _ _ h => H_plus2_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb106_bootstrap :
    Reaches bb106 initConfig (Scfg 1 0 1 (5 :: rep 8 1 [])) 131 := rfl

theorem bb106_halts_gt_f_omega2_plus_3_7 :
    ValidTM 10 6 bb106 ∧ ∃ t, HaltsIn bb106 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb106_valid, ?_⟩
  have hboot := bb106_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 0 1 (rep 7 1 [])
  have hm1_7 : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H51_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 1 H51
    (fun _ _ h => H51_mono h) rule_51 7 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb106) (mark' := 1) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 3 7 < iter H51 7 7 :=
    iter_strict_dom H51 (f_omega2_plus 2) 1 H51_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt2 : iter H51 7 7 ≤ iter H51 7 m1 := iter_mono_arg H51 (fun _ _ h => H51_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 3 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb106_halts_gt_f_omega2_plus_3_7

end BB10_6
end BB
