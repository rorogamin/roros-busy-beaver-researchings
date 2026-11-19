/-
  BB/BB11_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(11, 9):
    TM: 7LB3LB2LH2RA4LB6RI6LH7LH8LH_8RK3RB1LD2RA3LF5RB3RC3RC3RC_3RB1LB3LC2RC4LC1LE2RA3RE3RD_3RB3RE3LC2RC6LD3RD3RB5LF3RE_5RB3RE4RG4LC3LG5LE3RF3RF2RA_5RB1RJ2RA1LF5LF5LF2RH2RA5LF_5LF4RG1LB1LG7LG5LG2LH6LD7LG_1RC2RF1LH1LH2LH5RG5LF7RJ4LC_1RZ5LJ1LI1LI1RZ5RH1LI6LK1RZ_7LA5LA8LJ8LJ1RZ5RB8LJ3LK8LJ_8LJ7RG6LK6LK5RC5RE6LK0RD7RJ
    Domain: BB(11, 9) (11 states, 9 symbols)
    Previous best dominated bounds: BB(10, 9) > f_{ω^2+6}(7), BB(11, 8) > f_{ω^2+6}(10)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+7}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB11_9

def bb119 : TM
  -- State A (0): 7LB 3LB 2LH 2RA 4LB 6RI 6LH 7LH 8LH
  | 0, 0 => some ⟨7, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  | 0, 7 => some ⟨7, Dir.L, some 7⟩
  | 0, 8 => some ⟨8, Dir.L, some 7⟩
  -- State B (1): 8RK 3RB 1LD 2RA 3LF 5RB 3RC 3RC 3RC
  | 1, 0 => some ⟨8, Dir.R, some 10⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨3, Dir.R, some 2⟩
  | 1, 7 => some ⟨3, Dir.R, some 2⟩
  | 1, 8 => some ⟨3, Dir.R, some 2⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 3RE 3RD
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨2, Dir.R, some 0⟩
  | 2, 7 => some ⟨3, Dir.R, some 4⟩
  | 2, 8 => some ⟨3, Dir.R, some 3⟩
  -- State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 5LF 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 3⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨3, Dir.R, some 1⟩
  | 3, 7 => some ⟨5, Dir.L, some 5⟩
  | 3, 8 => some ⟨3, Dir.R, some 4⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 3RF 3RF 2RA
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨3, Dir.R, some 5⟩
  | 4, 7 => some ⟨3, Dir.R, some 5⟩
  | 4, 8 => some ⟨2, Dir.R, some 0⟩
  -- State F (5): 5RB 1RJ 2RA 1LF 5LF 5LF 2RH 2RA 5LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, some 9⟩
  | 5, 2 => some ⟨2, Dir.R, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨2, Dir.R, some 7⟩
  | 5, 7 => some ⟨2, Dir.R, some 0⟩
  | 5, 8 => some ⟨5, Dir.L, some 5⟩
  -- State G (6): 5LF 4RG 1LB 1LG 7LG 5LG 2LH 6LD 7LG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨7, Dir.L, some 6⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  | 6, 7 => some ⟨6, Dir.L, some 3⟩
  | 6, 8 => some ⟨7, Dir.L, some 6⟩
  -- State H (7): 1RC 2RF 1LH 1LH 2LH 5RG 5LF 7RJ 4LC
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.R, some 5⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨5, Dir.L, some 5⟩
  | 7, 7 => some ⟨7, Dir.R, some 9⟩
  | 7, 8 => some ⟨4, Dir.L, some 2⟩
  -- State I (8): 1RZ 5LJ 1LI 1LI 1RZ 5RH 1LI 6LK 1RZ
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 9⟩
  | 8, 2 => some ⟨1, Dir.L, some 8⟩
  | 8, 3 => some ⟨1, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.R, none⟩
  | 8, 5 => some ⟨5, Dir.R, some 7⟩
  | 8, 6 => some ⟨1, Dir.L, some 8⟩
  | 8, 7 => some ⟨6, Dir.L, some 10⟩
  | 8, 8 => some ⟨1, Dir.R, none⟩
  -- State J (9): 7LA 5LA 8LJ 8LJ 1RZ 5RB 8LJ 3LK 8LJ
  | 9, 0 => some ⟨7, Dir.L, some 0⟩
  | 9, 1 => some ⟨5, Dir.L, some 0⟩
  | 9, 2 => some ⟨8, Dir.L, some 9⟩
  | 9, 3 => some ⟨8, Dir.L, some 9⟩
  | 9, 4 => some ⟨1, Dir.R, none⟩
  | 9, 5 => some ⟨5, Dir.R, some 1⟩
  | 9, 6 => some ⟨8, Dir.L, some 9⟩
  | 9, 7 => some ⟨3, Dir.L, some 10⟩
  | 9, 8 => some ⟨8, Dir.L, some 9⟩
  -- State K (10): 8LJ 7RG 6LK 6LK 5RC 5RE 6LK 0RD 7RJ
  | 10, 0 => some ⟨8, Dir.L, some 9⟩
  | 10, 1 => some ⟨7, Dir.R, some 6⟩
  | 10, 2 => some ⟨6, Dir.L, some 10⟩
  | 10, 3 => some ⟨6, Dir.L, some 10⟩
  | 10, 4 => some ⟨5, Dir.R, some 2⟩
  | 10, 5 => some ⟨5, Dir.R, some 4⟩
  | 10, 6 => some ⟨6, Dir.L, some 10⟩
  | 10, 7 => some ⟨0, Dir.R, some 3⟩
  | 10, 8 => some ⟨7, Dir.R, some 9⟩
  | _, _ => none

theorem bb119_valid : ValidTM 11 9 bb119 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 8 => match sym with | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 | 4 | 8 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 11 => rfl

theorem bb119_core : Fwp2_H8Core bb119 :=
  ⟨⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
     rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def H51 (m : Nat) : Nat := iter H8_H (2 * m - 1) 1

theorem H51_mono {x y : Nat} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H8_H (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H8_H_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 4 m < H51 m :=
  climb_2m_minus_1 H8_H (f_omega2_plus 3) 1 (by omega) (fun _ _ h => H8_H_mono h) H8_H_inc H8_H_gt
    (fOmega2_props 1 0 3) m hm

theorem H51_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H51 m := by
  have h1 := H51_gt m hm; have h2 : m ≤ f_omega2_plus 4 m := (fOmega2_props 1 0 4).ge_self m; omega

theorem H51_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H51 m :=
  iter_H_ge_17 H8_H (2 * m - 1) 1 (by omega) (by omega) H8_H_inc H8_H_ge_17

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb119 (Scfg (r + 2) 0 m (5 :: 1 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb119) (sw := 9) (mark' := 5) (low' := 7)
    (s1 := 2) (s2 := 3) (s3 := 4) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_8_H_rep bb119_core (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

def H5mid (m : Nat) : Nat := iter H51 (2 * m + 1) 1

theorem H5mid_mono {x y : Nat} (hxy : x ≤ y) : H5mid x ≤ H5mid y :=
  iter_mono_steps H51 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H51_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H5mid_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 5 m < H5mid m :=
  climb_2m_plus_1 H51 (f_omega2_plus 4) 1 (by omega) (fun _ _ h => H51_mono h) H51_inc H51_gt
    (fOmega2_props 1 0 4) m hm

theorem H5mid_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H5mid m := by
  have h1 := H5mid_gt m hm; have h2 : m ≤ f_omega2_plus 5 m := (fOmega2_props 1 0 5).ge_self m; omega

theorem H5mid_ge_17 (m : Nat) : 17 ≤ H5mid m :=
  iter_H_ge_17 H51 (2 * m + 1) 1 (by omega) (by omega) H51_inc H51_ge_17

theorem rule_5mid (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb119 (Scfg (r + 2) 0 m (5 :: 6 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H5mid m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5mark_empty (tm := bb119) (mark' := 5) bb119_core.h7.h6.fh.fp
    rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m R
  have hpe : 1 ≤ Pempty (r + 1) := Nat.le_trans (by omega) (Pempty_ge (r + 1))
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 2 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 (2 * m + 1) r (Pempty (r + 1)) R hpe
  have harg : H5mid m ≤ iter H51 (2 * m + 1) (Pempty (r + 1)) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

def H5top (m : Nat) : Nat := iter H5mid (2 * m + 1) 0

theorem H5top_mono {x y : Nat} (hxy : x ≤ y) : H5top x ≤ H5top y :=
  iter_mono_steps H5mid (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H5mid_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 0

theorem H5top_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 6 m < H5top m := by
  have hsplit : iter H5mid (2 * m + 1) 0 = iter H5mid (2 * m) (H5mid 0) := by
    rw [iter_add H5mid (2 * m) 1 0, iter_succ, iter_zero]
  have h0 : 1 ≤ H5mid 0 := Nat.le_trans (by omega : 1 ≤ 17) (H5mid_ge_17 0)
  have h1 := climb_double H5mid (f_omega2_plus 5) 1 (by omega) (fun _ _ h => H5mid_mono h) H5mid_inc H5mid_gt
    (fOmega2_props 1 0 5) m hm
  have h2 := iter_mono_arg H5mid (fun _ _ h => H5mid_mono h) (2 * m) h0
  unfold H5top; rw [hsplit]; exact Nat.lt_of_lt_of_le h1 h2

theorem H5top_ge_17 (m : Nat) : 17 ≤ H5top m := by
  unfold H5top; rw [iter_succ]; exact H5mid_ge_17 _

theorem rule_5top (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb119 (Scfg (r + 2) 0 m (5 :: 7 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H5top m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5top_zero (tm := bb119) (mark' := 5) (top := 7)
    (e1 := 4) (e2 := 5) (e3 := 7)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 2 6 H5mid
    (fun _ _ h => H5mid_mono h) rule_5mid (2 * m + 1) r 0 R
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb119_bootstrap :
    Reaches bb119 initConfig (Scfg 3 0 0 (1 :: 5 :: rep 8 7 [])) 84 := rfl

theorem bb119_halts_gt_f_omega2_plus_7_7 :
    ValidTM 11 9 bb119 ∧ ∃ t, HaltsIn bb119 initConfig t ∧ f_omega2_plus 7 7 < t := by
  refine ⟨bb119_valid, ?_⟩
  have hboot := bb119_bootstrap
  obtain ⟨t0, h0, _⟩ := fwp2_step bb119_core.h7.h6.fh.fp 3 0 0 (5 :: rep 8 7 [])
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5top 1 (Pfn 3 0 0) (rep 7 7 [])
  have hm1_k : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H5top_ge_17 _) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 2 7 H5top (fun _ _ h => H5top_mono h) rule_5top 7 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb119) (mark' := 5) rfl rfl (r2 + 2) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h0) h1) h2) hhalt
  have hlt1 : f_omega2_plus 7 7 < iter H5top 7 7 :=
    iter_strict_dom H5top (f_omega2_plus 6) 1 H5top_gt (fOmega2_props 1 0 6) 7 7 (by omega) (by omega)
  have hlt2 : iter H5top 7 7 ≤ iter H5top 7 m1 := iter_mono_arg H5top (fun _ _ h => H5top_mono h) 7 hm1_k
  have hlt_m2 : f_omega2_plus 7 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb119_halts_gt_f_omega2_plus_7_7

end BB11_9
end BB
