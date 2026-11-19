/-
  BB/BB2_18.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 18):
    Domain: BB(2, 18) (2 states, 18 symbols)
    Previous best dominated bound: our BB(2, 17) > f_ω(f_7(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_8(2))
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_18

def bb218 : TM
  | 0, 0  => some ⟨9, Dir.L, some 1⟩
  | 0, 1  => some ⟨5, Dir.L, some 0⟩
  | 0, 2  => some ⟨1, Dir.L, some 1⟩
  | 0, 3  => some ⟨6, Dir.R, some 0⟩
  | 0, 4  => some ⟨3, Dir.R, some 0⟩
  | 0, 5  => some ⟨4, Dir.R, some 0⟩
  | 0, 6  => some ⟨2, Dir.R, some 1⟩
  | 0, 7  => some ⟨8, Dir.L, some 1⟩
  | 0, 8  => some ⟨5, Dir.L, some 0⟩
  | 0, 9  => some ⟨10, Dir.L, some 0⟩
  | 0, 10 => some ⟨17, Dir.R, some 0⟩
  | 0, 11 => some ⟨7, Dir.L, some 1⟩
  | 0, 12 => some ⟨11, Dir.L, some 1⟩
  | 0, 13 => some ⟨12, Dir.L, some 1⟩
  | 0, 14 => some ⟨13, Dir.L, some 1⟩
  | 0, 15 => some ⟨14, Dir.L, some 1⟩
  | 0, 16 => some ⟨15, Dir.L, some 1⟩
  | 0, 17 => some ⟨16, Dir.L, some 1⟩
  | 1, 0  => some ⟨4, Dir.R, some 0⟩
  | 1, 1  => some ⟨1, Dir.L, some 0⟩
  | 1, 2  => some ⟨3, Dir.L, some 1⟩
  | 1, 3  => some ⟨2, Dir.R, some 1⟩
  | 1, 4  => some ⟨2, Dir.R, some 1⟩
  | 1, 5  => some ⟨3, Dir.L, some 0⟩
  | 1, 6  => some ⟨3, Dir.L, some 1⟩
  | 1, 7  => some ⟨7, Dir.L, some 1⟩
  | 1, 8  => some ⟨8, Dir.L, some 1⟩
  | 1, 9  => some ⟨1, Dir.R, none⟩
  | 1, 10 => some ⟨17, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | 1, 12 => some ⟨12, Dir.L, some 1⟩
  | 1, 13 => some ⟨13, Dir.L, some 1⟩
  | 1, 14 => some ⟨14, Dir.L, some 1⟩
  | 1, 15 => some ⟨15, Dir.L, some 1⟩
  | 1, 16 => some ⟨16, Dir.L, some 1⟩
  | 1, 17 => some ⟨17, Dir.L, some 1⟩
  | _, _  => none

theorem bb218_valid : ValidTM 2 18 bb218 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => simp [bb218]
      | _ + 18 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => simp [bb218]
      | _ + 18 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => omega
      | _ + 18 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => omega
      | _ + 18 => rfl
    | _ + 2 => rfl

theorem bb218_core : Kropitz2Core bb218 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bb218_bootstrap :
    Reaches bb218 initConfig (B2cfg 8 0 [8, 9]) 204 := by
  have h1 : Reaches bb218 initConfig (mkCfgR (some 1) [] [4, 3, 3, 15, 9]) 25 := rfl
  have h2 : Reaches bb218 (mkCfgR (some 1) [] [4, 3, 3, 15, 9]) (mkCfgR (some 0) [4] [3, 3, 3, 3, 14, 9]) 25 := rfl
  have h3 : Reaches bb218 (mkCfgR (some 0) [4] [3, 3, 3, 3, 14, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 13, 9]) 25 := rfl
  have h4 : Reaches bb218 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 13, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 12, 9]) 25 := rfl
  have h5 : Reaches bb218 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 12, 9]) (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 11, 9]) 25 := rfl
  have h6 : Reaches bb218 (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 11, 9]) (mkCfgR (some 1) [2, 2, 2, 2, 2, 2] [2, 3, 7, 9]) 25 := rfl
  have h7 : Reaches bb218 (mkCfgR (some 1) [2, 2, 2, 2, 2, 2] [2, 3, 7, 9]) (mkCfgR (some 1) [] [4, 3, 3, 3, 3, 3, 3, 3, 3, 8, 9]) 25 := rfl
  have h8 : Reaches bb218 (mkCfgR (some 1) [] [4, 3, 3, 3, 3, 3, 3, 3, 3, 8, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 6, 4] [3, 3, 3, 3, 8, 9]) 25 := rfl
  have h9 : Reaches bb218 (mkCfgR (some 0) [6, 6, 6, 6, 6, 4] [3, 3, 3, 3, 8, 9]) (B2cfg 8 0 [8, 9]) 4 := rfl
  exact reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 (reaches_trans h8 (h9))))))))

theorem bb218_halts_gt_f_omega_f8_2 :
    ValidTM 2 18 bb218 ∧ ∃ s, HaltsIn bb218 initConfig s ∧ f_omega (fFin 8 2) < s := by
  refine ⟨bb218_valid, ?_⟩
  have hboot := bb218_bootstrap
  obtain ⟨m, hm⟩ : ∃ m, m = Kfn 8 0 := ⟨_, rfl⟩
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb218_core 8 0 [9]
  rw [← hm] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb218_core (w' := 16) rfl rfl rfl 8 m
  rw [(by omega : 2 * m + 8 + 1 = 2 * m + 9)] at h2
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb218_core (s := 17) (w' := 15) rfl rfl (2 * m + 9) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 9) + 1 = 2 * m + 10)] at h3
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb218_core (s := 16) (w' := 14) rfl rfl (2 * m + 10) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 10) + 1 = 2 * m + 11)] at h4
  obtain ⟨t5, h5, _⟩ := kropitz2_reload_gen bb218_core (s := 15) (w' := 13) rfl rfl (2 * m + 11) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 11) + 1 = 2 * m + 12)] at h5
  obtain ⟨t6, h6, _⟩ := kropitz2_reload_gen bb218_core (s := 14) (w' := 12) rfl rfl (2 * m + 12) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 12) + 1 = 2 * m + 13)] at h6
  obtain ⟨t7, h7, _⟩ := kropitz2_reload_gen bb218_core (s := 13) (w' := 11) rfl rfl (2 * m + 13) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 13) + 1 = 2 * m + 14)] at h7
  obtain ⟨t8, h8, _⟩ := kropitz2_reload_gen bb218_core (s := 12) (w' := 10) rfl rfl (2 * m + 14) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 14) + 1 = 2 * m + 15)] at h8
  obtain ⟨t9, h9, _⟩ := kropitz2_reload_gen bb218_core (s := 11) (w' := 6) rfl rfl (2 * m + 15) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 15) + 1 = 2 * m + 16)] at h9
  obtain ⟨t10, h10, _⟩ := kropitz2_reload_gen bb218_core (s := 7) (w' := 7) rfl rfl (2 * m + 16) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 16) + 1 = 2 * m + 17)] at h10
  obtain ⟨t11, h11, hle11⟩ := kropitz2_step_8 bb218_core (2 * m + 17) 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb218_core rfl rfl (2 * m + 17) (Kfn (2 * m + 17) 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 (reaches_trans h8 (reaches_trans h9 (reaches_trans h10 (reaches_trans h11 (hhalt))))))))))))
  have hfk : fFin 8 2 < Kfn 8 0 := Kfn_zero_gt_fFin2 8 (by omega)
  have hmono : f_omega (fFin 8 2) ≤ f_omega (2 * m + 16) :=
    (fOmegaMul_props 1 0).mono _ _ (by omega)
  have hgt : f_omega (2 * m + 16) < Kfn (2 * m + 17) 0 :=
    Kfn_zero_gt_fOmega (2 * m + 16)
  exact ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hgt (by omega))⟩

#print axioms bb218_halts_gt_f_omega_f8_2

end BB2_18
end BB
