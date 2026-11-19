/-
  BB/BB10_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(10, 7):
    TM: 2RH3LB2LH2RA4LB4RI6LH_4RJ3RB1LD2RA3LF5RB3RC_3RB1LB3LC2RC4LC1LE3RD_3RB3RE3LC2RC0LD3RD3RE_5RB3RE4RG4LC3LG5LE2RA_5RB1RJ1RD1LF5LF5LF1RZ_5LF4RG1LB1LG4LG5LG2LH_2RG2RF1LH1LH2LH5RG1RZ_1RZ5LJ1LI1LI1LI5RH1RZ_4LG5LA6LJ6LJ6LJ5RB1RZ
    Domain: BB(10, 7) (10 states, 7 symbols)
    Previous best dominated bounds: BB(9, 7) > f_{ω^2+3}(7), BB(10, 6) > f_{ω^2+3}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+4}(4)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB10_7

def bb107 : TM
  -- State A (0): 2RH 3LB 2LH 2RA 4LB 4RI 6LH
  | 0, 0 => some ⟨2, Dir.R, some 7⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  -- State B (1): 4RJ 3RB 1LD 2RA 3LF 5RB 3RC
  | 1, 0 => some ⟨4, Dir.R, some 9⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨3, Dir.R, some 2⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 3RD
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨3, Dir.R, some 3⟩
  -- State D (3): 3RB 3RE 3LC 2RC 0LD 3RD 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨0, Dir.L, some 3⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨3, Dir.R, some 4⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 2RA
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨2, Dir.R, some 0⟩
  -- State F (5): 5RB 1RJ 1RD 1LF 5LF 5LF 1RZ
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, some 9⟩
  | 5, 2 => some ⟨1, Dir.R, some 3⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨1, Dir.R, none⟩
  -- State G (6): 5LF 4RG 1LB 1LG 4LG 5LG 2LH
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  -- State H (7): 2RG 2RF 1LH 1LH 2LH 5RG 1RZ
  | 7, 0 => some ⟨2, Dir.R, some 6⟩
  | 7, 1 => some ⟨2, Dir.R, some 5⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨1, Dir.R, none⟩
  -- State I (8): 1RZ 5LJ 1LI 1LI 1LI 5RH 1RZ
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 9⟩
  | 8, 2 => some ⟨1, Dir.L, some 8⟩
  | 8, 3 => some ⟨1, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 8⟩
  | 8, 5 => some ⟨5, Dir.R, some 7⟩
  | 8, 6 => some ⟨1, Dir.R, none⟩
  -- State J (9): 4LG 5LA 6LJ 6LJ 6LJ 5RB 1RZ
  | 9, 0 => some ⟨4, Dir.L, some 6⟩
  | 9, 1 => some ⟨5, Dir.L, some 0⟩
  | 9, 2 => some ⟨6, Dir.L, some 9⟩
  | 9, 3 => some ⟨6, Dir.L, some 9⟩
  | 9, 4 => some ⟨6, Dir.L, some 9⟩
  | 9, 5 => some ⟨5, Dir.R, some 1⟩
  | 9, 6 => some ⟨1, Dir.R, none⟩
  | _, _ => none

theorem bb107_valid : ValidTM 10 7 bb107 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | _ + 10 => omega
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
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 10 => rfl

theorem bb107_core : Fwp2_H6Core bb107 :=
  ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl⟩

def H51 (m : Nat) : Nat := iter H_plus2 (2 * m - 1) 1

theorem H51_mono {x y : Nat} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps H_plus2 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H_plus2_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H51 m :=
  climb_2m_minus_1 H_plus2 (f_omega2_plus 1) 1 (by omega) (fun _ _ h => H_plus2_mono h) H_plus2_inc H_plus2_gt
    (fOmega2_props 1 0 1) m hm

theorem H51_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H51 m := by
  have h1 := H51_gt m hm; have h2 : m ≤ f_omega2_plus 2 m := (fOmega2_props 1 0 2).ge_self m; omega

theorem H51_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H51 m :=
  iter_H_ge_17 H_plus2 (2 * m - 1) 1 (by omega) (by omega) H_plus2_inc (fun z _ => H_plus2_ge_17 z)

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches bb107 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb107) (sw := 9) (mark' := 3) (low' := 5)
    (s1 := 2) (s2 := 3) (s3 := 4) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl r m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_H_rep bb107_core (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)).1 (Nat.le_add_left _ _)⟩

def H5mid (m : Nat) : Nat := iter H51 (2 * m + 1) 1

theorem H5mid_mono {x y : Nat} (hxy : x ≤ y) : H5mid x ≤ H5mid y :=
  iter_mono_steps H51 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H51_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H5mid_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 3 m < H5mid m :=
  climb_2m_plus_1 H51 (f_omega2_plus 2) 1 (by omega) (fun _ _ h => H51_mono h) H51_inc H51_gt
    (fOmega2_props 1 0 2) m hm

theorem H5mid_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H5mid m := by
  have h1 := H5mid_gt m hm; have h2 : m ≤ f_omega2_plus 3 m := (fOmega2_props 1 0 3).ge_self m; omega

theorem H5mid_ge_17 (m : Nat) : 17 ≤ H5mid m :=
  iter_H_ge_17 H51 (2 * m + 1) 1 (by omega) (by omega) H51_inc H51_ge_17

theorem rule_5mid (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb107 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H5mid m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5mark_empty (tm := bb107) (mark' := 3) bb107_core.fh.fp
    rfl rfl rfl rfl rfl rfl rfl rfl r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 (2 * m + 1) r (Pempty r) R hpe
  have harg : H5mid m ≤ iter H51 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb107_bootstrap :
    Reaches bb107 initConfig (Scfg 2 0 1 (5 :: rep 5 4 [])) 54 := rfl

theorem bb107_halts_gt_f_omega2_plus_4_4 :
    ValidTM 10 7 bb107 ∧ ∃ t, HaltsIn bb107 initConfig t ∧ f_omega2_plus 4 4 < t := by
  refine ⟨bb107_valid, ?_⟩
  have hboot := bb107_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5mid 1 1 (rep 4 4 [])
  have hm1_k : 4 ≤ m1 := Nat.le_trans (by omega : 4 ≤ 17) (Nat.le_trans (H5mid_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 4 H5mid (fun _ _ h => H5mid_mono h) rule_5mid 4 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb107) (mark' := 3) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 4 4 < iter H5mid 4 4 :=
    iter_strict_dom H5mid (f_omega2_plus 3) 1 H5mid_gt (fOmega2_props 1 0 3) 4 4 (by omega) (by omega)
  have hlt2 : iter H5mid 4 4 ≤ iter H5mid 4 m1 := iter_mono_arg H5mid (fun _ _ h => H5mid_mono h) 4 hm1_k
  have hlt_m2 : f_omega2_plus 4 4 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb107_halts_gt_f_omega2_plus_4_4

end BB10_7
end BB
