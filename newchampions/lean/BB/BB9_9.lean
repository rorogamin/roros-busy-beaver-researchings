/-
  BB/BB9_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(9, 9):
    TM: 8RH3LB2LH2RA4LB6RI6LH7LH8LH_1LF3RB1LD2RA3LF5RB3RC3RC3RC_3RB1LB3LC2RC4LC1LE2RA3RE3RD_3RB3RE3LC2RC6LD3RD3RB1RZ3RE_5RB3RE4RG4LC3LG5LE3LD3RF2RA_5RB5RB2RC1LF5LF5LF1RI2RA7RA_5LF4RG1LB1LG7LG5LG2LH6LD7LG_1RF1RZ1LH1LH2LH5RG1RZ1RZ1RZ_1RZ5LI8LI8LI8LE5RB8LI1RZ5RI
    Domain: BB(9, 9) (9 states, 9 symbols)
    Previous best dominated bounds: BB(8, 9) > f_{ω^2+4}(7), BB(9, 8) > f_{ω^2+4}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB9_9

def bb99 : TM
  -- State A (0): 8RH 3LB 2LH 2RA 4LB 6RI 6LH 7LH 8LH
  | 0, 0 => some ⟨8, Dir.R, some 7⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  | 0, 7 => some ⟨7, Dir.L, some 7⟩
  | 0, 8 => some ⟨8, Dir.L, some 7⟩
  -- State B (1): 1LF 3RB 1LD 2RA 3LF 5RB 3RC 3RC 3RC
  | 1, 0 => some ⟨1, Dir.L, some 5⟩
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
  -- State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 1RZ 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 3⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨3, Dir.R, some 1⟩
  | 3, 7 => some ⟨1, Dir.R, none⟩
  | 3, 8 => some ⟨3, Dir.R, some 4⟩
  -- State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 3LD 3RF 2RA
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.R, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨3, Dir.L, some 3⟩
  | 4, 7 => some ⟨3, Dir.R, some 5⟩
  | 4, 8 => some ⟨2, Dir.R, some 0⟩
  -- State F (5): 5RB 5RB 2RC 1LF 5LF 5LF 1RI 2RA 7RA
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨2, Dir.R, some 2⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨1, Dir.R, some 8⟩
  | 5, 7 => some ⟨2, Dir.R, some 0⟩
  | 5, 8 => some ⟨7, Dir.R, some 0⟩
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
  -- State H (7): 1RF 1RZ 1LH 1LH 2LH 5RG 1RZ 1RZ 1RZ
  | 7, 0 => some ⟨1, Dir.R, some 5⟩
  | 7, 1 => some ⟨1, Dir.R, none⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨1, Dir.R, none⟩
  | 7, 7 => some ⟨1, Dir.R, none⟩
  | 7, 8 => some ⟨1, Dir.R, none⟩
  -- State I (8): 1RZ 5LI 8LI 8LI 8LE 5RB 8LI 1RZ 5RI
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 8⟩
  | 8, 2 => some ⟨8, Dir.L, some 8⟩
  | 8, 3 => some ⟨8, Dir.L, some 8⟩
  | 8, 4 => some ⟨8, Dir.L, some 4⟩
  | 8, 5 => some ⟨5, Dir.R, some 1⟩
  | 8, 6 => some ⟨8, Dir.L, some 8⟩
  | 8, 7 => some ⟨1, Dir.R, none⟩
  | 8, 8 => some ⟨5, Dir.R, some 8⟩
  | _, _ => none

theorem bb99_valid : ValidTM 9 9 bb99 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 => exact ⟨by decide, by decide⟩ | 7 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 7 => match sym with | 0 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 1 | 6 | 7 | 8 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 8 => exact ⟨by decide, by decide⟩ | 0 | 7 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | _ + 9 => omega
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
    | _ + 9 => rfl

theorem bb99_core : Fwp2_H8Core bb99 :=
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
    ∃ r' m' t, Reaches bb99 (Scfg (r + 2) 0 m (5 :: 1 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb99) (sw := 8) (mark' := 5) (low' := 7)
    (s1 := 2) (s2 := 3) (s3 := 4) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (r + 1) m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_8_H_rep bb99_core (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb99_bootstrap :
    Reaches bb99 initConfig (Scfg 3 0 1 (5 :: rep 8 1 [])) 138 := rfl

theorem bb99_halts_gt_f_omega2_plus_5_7 :
    ValidTM 9 9 bb99 ∧ ∃ t, HaltsIn bb99 initConfig t ∧ f_omega2_plus 5 7 < t := by
  refine ⟨bb99_valid, ?_⟩
  have hboot := bb99_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 1 1 (rep 7 1 []) (by omega)
  have hm1_k : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H51_ge_17 1 (by omega)) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 2 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 7 r1 m1 [] (by omega)
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb99) (mark' := 5) rfl rfl (r2 + 2) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 5 7 < iter H51 7 7 :=
    iter_strict_dom H51 (f_omega2_plus 4) 1 H51_gt (fOmega2_props 1 0 4) 7 7 (by omega) (by omega)
  have hlt2 : iter H51 7 7 ≤ iter H51 7 m1 := iter_mono_arg H51 (fun _ _ h => H51_mono h) 7 hm1_k
  have hlt_m2 : f_omega2_plus 5 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb99_halts_gt_f_omega2_plus_5_7

end BB9_9
end BB
