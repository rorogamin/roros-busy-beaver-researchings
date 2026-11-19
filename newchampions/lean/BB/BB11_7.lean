/-
  BB/BB11_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(11, 7):
    TM: 2RK3LB2LH2RA4LB4RI6LH_6LJ3RB1LD2RA3LF5RB3RC_3RB1LB3LC2RC4LC1LE3RD_3RB3RE3LC2RC3RG3RD3RE_5RB3RE4RG4LC3LG5LE2RA_5RB1RJ2RA1LF5LF5LF5LH_5LF4RG1LB1LG2RF5LG2LH_2RD2RF1LH1LH2LH5RG6RF_1RZ5LJ1LI1LI1LI5RH4LK_1LA5LA6LJ6LJ6LJ5RB6RF_6LC5LH4LK4LK4LK5RD2LB
    Domain: BB(11, 7) (11 states, 7 symbols)
    Previous best dominated bounds: BB(10, 7) > f_{ω^2+4}(4), BB(11, 6) > f_{ω^2+4}(8)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB11_7

def bb117 : TM
  -- State A (0): 2RK 3LB 2LH 2RA 4LB 4RI 6LH
  | 0, 0 => some ⟨2, Dir.R, some 10⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  -- State B (1): 6LJ 3RB 1LD 2RA 3LF 5RB 3RC
  | 1, 0 => some ⟨6, Dir.L, some 9⟩
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
  -- State D (3): 3RB 3RE 3LC 2RC 3RG 3RD 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨3, Dir.R, some 6⟩
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
  -- State F (5): 5RB 1RJ 2RA 1LF 5LF 5LF 5LH
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, some 9⟩
  | 5, 2 => some ⟨2, Dir.R, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 7⟩
  -- State G (6): 5LF 4RG 1LB 1LG 2RF 5LG 2LH
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 5⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  -- State H (7): 2RD 2RF 1LH 1LH 2LH 5RG 6RF
  | 7, 0 => some ⟨2, Dir.R, some 3⟩
  | 7, 1 => some ⟨2, Dir.R, some 5⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨6, Dir.R, some 5⟩
  -- State I (8): 1RZ 5LJ 1LI 1LI 1LI 5RH 4LK
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 9⟩
  | 8, 2 => some ⟨1, Dir.L, some 8⟩
  | 8, 3 => some ⟨1, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 8⟩
  | 8, 5 => some ⟨5, Dir.R, some 7⟩
  | 8, 6 => some ⟨4, Dir.L, some 10⟩
  -- State J (9): 1LA 5LA 6LJ 6LJ 6LJ 5RB 6RF
  | 9, 0 => some ⟨1, Dir.L, some 0⟩
  | 9, 1 => some ⟨5, Dir.L, some 0⟩
  | 9, 2 => some ⟨6, Dir.L, some 9⟩
  | 9, 3 => some ⟨6, Dir.L, some 9⟩
  | 9, 4 => some ⟨6, Dir.L, some 9⟩
  | 9, 5 => some ⟨5, Dir.R, some 1⟩
  | 9, 6 => some ⟨6, Dir.R, some 5⟩
  -- State K (10): 6LC 5LH 4LK 4LK 4LK 5RD 2LB
  | 10, 0 => some ⟨6, Dir.L, some 2⟩
  | 10, 1 => some ⟨5, Dir.L, some 7⟩
  | 10, 2 => some ⟨4, Dir.L, some 10⟩
  | 10, 3 => some ⟨4, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.L, some 10⟩
  | 10, 5 => some ⟨5, Dir.R, some 3⟩
  | 10, 6 => some ⟨2, Dir.L, some 1⟩
  | _, _ => none

theorem bb117_valid : ValidTM 11 7 bb117 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | _ + 11 => omega
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
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 11 => rfl

theorem bb117_core : Fwp2_H6Core bb117 :=
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
    ∃ r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb117) (sw := 9) (mark' := 3) (low' := 5)
    (s1 := 2) (s2 := 3) (s3 := 4) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl r m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_H_rep bb117_core (2 * m - 1) r 1 (5 :: R) (by omega)
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
    ∃ r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H5mid m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5mark_empty (tm := bb117) (mark' := 3) bb117_core.fh.fp
    rfl rfl rfl rfl rfl rfl rfl rfl r m R
  have hpe : 1 ≤ Pempty r := Nat.le_trans (by omega) (Pempty_ge r)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 (2 * m + 1) r (Pempty r) R hpe
  have harg : H5mid m ≤ iter H51 (2 * m + 1) (Pempty r) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

def H5top (m : Nat) : Nat := iter H5mid (2 * m + 1) 0

theorem H5top_mono {x y : Nat} (hxy : x ≤ y) : H5top x ≤ H5top y :=
  iter_mono_steps H5mid (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H5mid_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 0

theorem H5top_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 4 m < H5top m := by
  have hsplit : iter H5mid (2 * m + 1) 0 = iter H5mid (2 * m) (H5mid 0) := by
    rw [iter_add H5mid (2 * m) 1 0, iter_succ, iter_zero]
  have h0 : 1 ≤ H5mid 0 := Nat.le_trans (by omega : 1 ≤ 17) (H5mid_ge_17 0)
  have h1 := climb_double H5mid (f_omega2_plus 3) 1 (by omega) (fun _ _ h => H5mid_mono h) H5mid_inc H5mid_gt
    (fOmega2_props 1 0 3) m hm
  have h2 := iter_mono_arg H5mid (fun _ _ h => H5mid_mono h) (2 * m) h0
  unfold H5top; rw [hsplit]; exact Nat.lt_of_lt_of_le h1 h2

theorem H5top_ge_17 (m : Nat) : 17 ≤ H5top m := by
  unfold H5top; rw [iter_succ]; exact H5mid_ge_17 _

theorem rule_5top (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 6 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H5top m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5top_zero (tm := bb117) (mark' := 3) (top := 6)
    (e1 := 3) (e2 := 6) (e3 := 5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl r m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 4 H5mid
    (fun _ _ h => H5mid_mono h) rule_5mid (2 * m + 1) r 0 R
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb117_bootstrap :
    Reaches bb117 initConfig (Scfg 1 0 1 (5 :: rep 8 6 [])) 57 := rfl

theorem bb117_halts_gt_f_omega2_plus_5_7 :
    ValidTM 11 7 bb117 ∧ ∃ t, HaltsIn bb117 initConfig t ∧ f_omega2_plus 5 7 < t := by
  refine ⟨bb117_valid, ?_⟩
  have hboot := bb117_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5top 0 1 (rep 7 6 [])
  have hm1_k : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H5top_ge_17 1) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 1 6 H5top (fun _ _ h => H5top_mono h) rule_5top 7 r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb117) (mark' := 3) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 5 7 < iter H5top 7 7 :=
    iter_strict_dom H5top (f_omega2_plus 4) 1 H5top_gt (fOmega2_props 1 0 4) 7 7 (by omega) (by omega)
  have hlt2 : iter H5top 7 7 ≤ iter H5top 7 m1 := iter_mono_arg H5top (fun _ _ h => H5top_mono h) 7 hm1_k
  have hlt_m2 : f_omega2_plus 5 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb117_halts_gt_f_omega2_plus_5_7

end BB11_7
end BB
