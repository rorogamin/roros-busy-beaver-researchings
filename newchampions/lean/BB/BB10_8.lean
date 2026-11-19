/-
  BB/BB10_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(10, 8):
    TM: 1RJ3LB2LH2RA4LB6RI6LH7LH_7LE3RB1LD2RA3LF5RB3RC3RC_3RB1LB3LC2RC4LC1LE2RA3RE_3RB3RE3LC2RC6LD3RD3RB7RB_5RB3RE4RG4LC3LG5LE6LH3RF_5RB1RJ7RI1LF5LF5LF0LD2RA_5LF4RG1LB1LG5RJ5LG2LH6LD_7RH2RF1LH1LH2LH5RG3RJ6RH_1RZ5LJ1LI1LI6LB5RH1LI5RH_4RF5LA7LJ7LJ1RZ5RB7LJ6LG
    Domain: BB(10, 8) (10 states, 8 symbols)
    Previous best dominated bounds: BB(9, 8) > f_{ω^2+4}(7), BB(10, 7) > f_{ω^2+4}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB10_8

def bb108 : TM
  -- State A (0): 1RJ 3LB 2LH 2RA 4LB 6RI 6LH 7LH
  | 0, 0 => some ⟨1, Dir.R, some 9⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  | 0, 7 => some ⟨7, Dir.L, some 7⟩
  -- State B (1): 7LE 3RB 1LD 2RA 3LF 5RB 3RC 3RC
  | 1, 0 => some ⟨7, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨3, Dir.R, some 2⟩
  | 1, 7 => some ⟨3, Dir.R, some 2⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 3RE
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨2, Dir.R, some 0⟩
  | 2, 7 => some ⟨3, Dir.R, some 4⟩
  -- State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 7RB
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 3⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨3, Dir.R, some 1⟩
  | 3, 7 => some ⟨7, Dir.R, some 1⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 6LH 3RF
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨6, Dir.L, some 7⟩
  | 4, 7 => some ⟨3, Dir.R, some 5⟩
  -- State F (5): 5RB 1RJ 7RI 1LF 5LF 5LF 0LD 2RA
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, some 9⟩
  | 5, 2 => some ⟨7, Dir.R, some 8⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨0, Dir.L, some 3⟩
  | 5, 7 => some ⟨2, Dir.R, some 0⟩
  -- State G (6): 5LF 4RG 1LB 1LG 5RJ 5LG 2LH 6LD
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.R, some 9⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  | 6, 7 => some ⟨6, Dir.L, some 3⟩
  -- State H (7): 7RH 2RF 1LH 1LH 2LH 5RG 3RJ 6RH
  | 7, 0 => some ⟨7, Dir.R, some 7⟩
  | 7, 1 => some ⟨2, Dir.R, some 5⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨3, Dir.R, some 9⟩
  | 7, 7 => some ⟨6, Dir.R, some 7⟩
  -- State I (8): 1RZ 5LJ 1LI 1LI 6LB 5RH 1LI 5RH
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 9⟩
  | 8, 2 => some ⟨1, Dir.L, some 8⟩
  | 8, 3 => some ⟨1, Dir.L, some 8⟩
  | 8, 4 => some ⟨6, Dir.L, some 1⟩
  | 8, 5 => some ⟨5, Dir.R, some 7⟩
  | 8, 6 => some ⟨1, Dir.L, some 8⟩
  | 8, 7 => some ⟨5, Dir.R, some 7⟩
  -- State J (9): 4RF 5LA 7LJ 7LJ 1RZ 5RB 7LJ 6LG
  | 9, 0 => some ⟨4, Dir.R, some 5⟩
  | 9, 1 => some ⟨5, Dir.L, some 0⟩
  | 9, 2 => some ⟨7, Dir.L, some 9⟩
  | 9, 3 => some ⟨7, Dir.L, some 9⟩
  | 9, 4 => some ⟨1, Dir.R, none⟩
  | 9, 5 => some ⟨5, Dir.R, some 1⟩
  | 9, 6 => some ⟨7, Dir.L, some 9⟩
  | 9, 7 => some ⟨6, Dir.L, some 6⟩
  | _, _ => none

theorem bb108_valid : ValidTM 10 8 bb108 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 10 => rfl

theorem bb108_core : Fwp2_H7Core bb108 :=
  ⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

def H51 (m : Nat) : Nat := iter H7_H (2 * m - 1) 1

theorem H51_mono {x y : Nat} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H7_H (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_H_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 3 m < H51 m :=
  climb_2m_minus_1 H7_H (f_omega2_plus 2) 1 (by omega) (fun _ _ h => H7_H_mono h) H7_H_inc H7_H_gt
    (fOmega2_props 1 0 2) m hm

theorem H51_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H51 m := by
  have h1 := H51_gt m hm; have h2 : m ≤ f_omega2_plus 3 m := (fOmega2_props 1 0 3).ge_self m; omega

theorem H51_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H51 m :=
  iter_H_ge_17 H7_H (2 * m - 1) 1 (by omega) (by omega) H7_H_inc H7_H_ge_17

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb108 (Scfg (r + 2) 0 m (5 :: 1 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb108) (sw := 9) (mark' := 5) (low' := 6)
    (s1 := 2) (s2 := 4) (s3 := 5) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_7_H_rep bb108_core (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

def H5mid (m : Nat) : Nat := iter H51 (2 * m + 1) 1

theorem H5mid_mono {x y : Nat} (hxy : x ≤ y) : H5mid x ≤ H5mid y :=
  iter_mono_steps H51 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H51_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H5mid_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 4 m < H5mid m :=
  climb_2m_plus_1 H51 (f_omega2_plus 3) 1 (by omega) (fun _ _ h => H51_mono h) H51_inc H51_gt
    (fOmega2_props 1 0 3) m hm

theorem H5mid_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H5mid m := by
  have h1 := H5mid_gt m hm; have h2 : m ≤ f_omega2_plus 4 m := (fOmega2_props 1 0 4).ge_self m; omega

theorem H5mid_ge_17 (m : Nat) : 17 ≤ H5mid m :=
  iter_H_ge_17 H51 (2 * m + 1) 1 (by omega) (by omega) H51_inc H51_ge_17

theorem rule_5mid (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb108 (Scfg (r + 2) 0 m (5 :: 6 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H5mid m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5mark_empty (tm := bb108) (mark' := 5) bb108_core.h6.fh.fp
    rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m R
  have hpe : 1 ≤ Pempty (r + 1) := Nat.le_trans (by omega) (Pempty_ge (r + 1))
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 2 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 (2 * m + 1) r (Pempty (r + 1)) R hpe
  have harg : H5mid m ≤ iter H51 (2 * m + 1) (Pempty (r + 1)) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb108_bootstrap :
    Reaches bb108 initConfig (Scfg 2 0 1 (5 :: rep 8 6 [])) 196 := rfl

theorem bb108_halts_gt_f_omega2_plus_5_7 :
    ValidTM 10 8 bb108 ∧ ∃ t, HaltsIn bb108 initConfig t ∧ f_omega2_plus 5 7 < t := by
  refine ⟨bb108_valid, ?_⟩
  have hboot := bb108_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5mid 0 1 (rep 7 6 [])
  have hm1_k : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H5mid_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 2 6 H5mid (fun _ _ h => H5mid_mono h) rule_5mid 7 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb108) (mark' := 5) rfl rfl (r2 + 2) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 5 7 < iter H5mid 7 7 :=
    iter_strict_dom H5mid (f_omega2_plus 4) 1 H5mid_gt (fOmega2_props 1 0 4) 7 7 (by omega) (by omega)
  have hlt2 : iter H5mid 7 7 ≤ iter H5mid 7 m1 := iter_mono_arg H5mid (fun _ _ h => H5mid_mono h) 7 hm1_k
  have hlt_m2 : f_omega2_plus 5 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb108_halts_gt_f_omega2_plus_5_7

end BB10_8
end BB
