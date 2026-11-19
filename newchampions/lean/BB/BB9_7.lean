/-
  BB/BB9_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(9, 7):
    TM: 2RH3LB2LH2RA4LB4RI6LH_1LH3RB1LD2RA3LF5RB3RC_3RB1LB3LC2RC4LC1LE3RD_3RB3RE3LC2RC3LC3RD3RE_5RB3RE4RG4LC3LG5LE2RA_5RB5RB6RD1LF5LF5LF6RE_5LF4RG1LB1LG6RI5LG2LH_1LF6RC1LH1LH2LH5RG5LE_1RZ5LI6LI6LI6LI5RB1RZ
    Domain: BB(9, 7) (9 states, 7 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{ω^2+2}(8), BB(9, 6) > f_{ω^2+2}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace BB9_7

def bb97 : TM
  -- State A (0): 2RH 3LB 2LH 2RA 4LB 4RI 6LH
  | 0, 0 => some ⟨2, Dir.R, some 7⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 7⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.R, some 8⟩
  | 0, 6 => some ⟨6, Dir.L, some 7⟩
  -- State B (1): 1LH 3RB 1LD 2RA 3LF 5RB 3RC
  | 1, 0 => some ⟨1, Dir.L, some 7⟩
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
  -- State D (3): 3RB 3RE 3LC 2RC 3LC 3RD 3RE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨3, Dir.L, some 2⟩
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
  -- State F (5): 5RB 5RB 6RD 1LF 5LF 5LF 6RE
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨6, Dir.R, some 3⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨5, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨6, Dir.R, some 4⟩
  -- State G (6): 5LF 4RG 1LB 1LG 6RI 5LG 2LH
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨6, Dir.R, some 8⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨2, Dir.L, some 7⟩
  -- State H (7): 1LF 6RC 1LH 1LH 2LH 5RG 5LE
  | 7, 0 => some ⟨1, Dir.L, some 5⟩
  | 7, 1 => some ⟨6, Dir.R, some 2⟩
  | 7, 2 => some ⟨1, Dir.L, some 7⟩
  | 7, 3 => some ⟨1, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 7, 5 => some ⟨5, Dir.R, some 6⟩
  | 7, 6 => some ⟨5, Dir.L, some 4⟩
  -- State I (8): 1RZ 5LI 6LI 6LI 6LI 5RB 1RZ
  | 8, 0 => some ⟨1, Dir.R, none⟩
  | 8, 1 => some ⟨5, Dir.L, some 8⟩
  | 8, 2 => some ⟨6, Dir.L, some 8⟩
  | 8, 3 => some ⟨6, Dir.L, some 8⟩
  | 8, 4 => some ⟨6, Dir.L, some 8⟩
  | 8, 5 => some ⟨5, Dir.R, some 1⟩
  | 8, 6 => some ⟨1, Dir.R, none⟩
  | _, _ => none

theorem bb97_valid : ValidTM 9 7 bb97 := by
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
    | 8 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 | 6 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | _ + 9 => omega
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
    | _ + 9 => rfl

theorem bb97_core : Fwp2_H6Core bb97 :=
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
    ∃ r' m' t, Reaches bb97 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := bb97) (sw := 8) (mark' := 3) (low' := 5)
    (s1 := 2) (s2 := 3) (s3 := 4) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl r m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_6_H_rep bb97_core (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)).1 (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb97_bootstrap :
    Reaches bb97 initConfig (Scfg 1 0 1 (5 :: rep 8 1 [])) 76 := rfl

theorem bb97_halts_gt_f_omega2_plus_3_7 :
    ValidTM 9 7 bb97 ∧ ∃ t, HaltsIn bb97 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb97_valid, ?_⟩
  have hboot := bb97_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 0 1 (rep 7 1 []) (by omega)
  have hm1_k : 7 ≤ m1 := Nat.le_trans (by omega : 7 ≤ 17) (Nat.le_trans (H51_ge_17 1 (by omega)) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep 1 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 7 r1 m1 [] (by omega)
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := bb97) (mark' := 3) rfl rfl (r2 + 1) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 3 7 < iter H51 7 7 :=
    iter_strict_dom H51 (f_omega2_plus 2) 1 H51_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt2 : iter H51 7 7 ≤ iter H51 7 m1 := iter_mono_arg H51 (fun _ _ h => H51_mono h) 7 hm1_k
  have hlt_m2 : f_omega2_plus 3 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb97_halts_gt_f_omega2_plus_3_7

end BB9_7
end BB
