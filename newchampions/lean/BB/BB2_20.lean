/-
  BB/BB2_20.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 20):
    Domain: BB(2, 20) (2 states, 20 symbols)
    Previous best dominated bound: our BB(2, 19) > f_ω(f_9(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_10(2))
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_20

def bb220 : TM
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
  | 0, 10 => some ⟨19, Dir.R, some 0⟩
  | 0, 11 => some ⟨7, Dir.L, some 1⟩
  | 0, 12 => some ⟨11, Dir.L, some 1⟩
  | 0, 13 => some ⟨12, Dir.L, some 1⟩
  | 0, 14 => some ⟨13, Dir.L, some 1⟩
  | 0, 15 => some ⟨14, Dir.L, some 1⟩
  | 0, 16 => some ⟨15, Dir.L, some 1⟩
  | 0, 17 => some ⟨16, Dir.L, some 1⟩
  | 0, 18 => some ⟨17, Dir.L, some 1⟩
  | 0, 19 => some ⟨18, Dir.L, some 1⟩
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
  | 1, 10 => some ⟨19, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | 1, 12 => some ⟨12, Dir.L, some 1⟩
  | 1, 13 => some ⟨13, Dir.L, some 1⟩
  | 1, 14 => some ⟨14, Dir.L, some 1⟩
  | 1, 15 => some ⟨15, Dir.L, some 1⟩
  | 1, 16 => some ⟨16, Dir.L, some 1⟩
  | 1, 17 => some ⟨17, Dir.L, some 1⟩
  | 1, 18 => some ⟨18, Dir.L, some 1⟩
  | 1, 19 => some ⟨19, Dir.L, some 1⟩
  | _, _  => none

theorem bb220_valid : ValidTM 2 20 bb220 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => simp [bb220]
      | _ + 20 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => simp [bb220]
      | _ + 20 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => omega
      | _ + 20 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => omega
      | _ + 20 => rfl
    | _ + 2 => rfl

theorem bb220_core : Kropitz2Core bb220 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bb220_bootstrap :
    Reaches bb220 initConfig (B2cfg 10 0 [8, 9]) 292 := by
  have h1 : Reaches bb220 initConfig (mkCfgR (some 1) [2] [3, 18, 9]) 15 := rfl
  have h2 : Reaches bb220 (mkCfgR (some 1) [2] [3, 18, 9]) (mkCfgR (some 1) [2] [2, 3, 17, 9]) 15 := rfl
  have h3 : Reaches bb220 (mkCfgR (some 1) [2] [2, 3, 17, 9]) (mkCfgR (some 1) [2, 2, 2] [2, 16, 9]) 15 := rfl
  have h4 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2] [2, 16, 9]) (mkCfgR (some 1) [2] [3, 3, 3, 3, 15, 9]) 15 := rfl
  have h5 : Reaches bb220 (mkCfgR (some 1) [2] [3, 3, 3, 3, 15, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 15, 9]) 15 := rfl
  have h6 : Reaches bb220 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 15, 9]) (mkCfgR (some 1) [2, 2, 2, 2] [2, 3, 14, 9]) 15 := rfl
  have h7 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2, 2] [2, 3, 14, 9]) (mkCfgR (some 1) [6, 6, 6, 4] [6, 3, 3, 13, 9]) 15 := rfl
  have h8 : Reaches bb220 (mkCfgR (some 1) [6, 6, 6, 4] [6, 3, 3, 13, 9]) (mkCfgR (some 1) [2, 2, 2] [2, 3, 3, 3, 13, 9]) 15 := rfl
  have h9 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2] [2, 3, 3, 3, 13, 9]) (mkCfgR (some 1) [6, 6, 6, 6, 4] [6, 3, 3, 12, 9]) 15 := rfl
  have h10 : Reaches bb220 (mkCfgR (some 1) [6, 6, 6, 6, 4] [6, 3, 3, 12, 9]) (mkCfgR (some 1) [2, 2, 2, 2, 2, 2] [2, 3, 12, 9]) 15 := rfl
  have h11 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2, 2, 2, 2] [2, 3, 12, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 6, 6, 6, 4] [3, 12, 9]) 15 := rfl
  have h12 : Reaches bb220 (mkCfgR (some 0) [6, 6, 6, 6, 6, 6, 6, 4] [3, 12, 9]) (mkCfgR (some 1) [2, 2, 2, 2, 2] [3, 3, 3, 3, 11, 9]) 15 := rfl
  have h13 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2, 2, 2] [3, 3, 3, 3, 11, 9]) (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 9]) 15 := rfl
  have h14 : Reaches bb220 (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 9]) (mkCfgR (some 1) [6, 6, 6, 4] [6, 3, 3, 3, 3, 3, 7, 9]) 15 := rfl
  have h15 : Reaches bb220 (mkCfgR (some 1) [6, 6, 6, 4] [6, 3, 3, 3, 3, 3, 7, 9]) (mkCfgR (some 1) [2, 2, 2, 2, 2, 2, 2, 2, 2] [2, 7, 9]) 15 := rfl
  have h16 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2, 2, 2, 2, 2, 2, 2] [2, 7, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 3, 3, 7, 9]) 15 := rfl
  have h17 : Reaches bb220 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 3, 3, 7, 9]) (mkCfgR (some 1) [6, 4] [6, 3, 3, 3, 3, 3, 3, 3, 3, 8, 9]) 15 := rfl
  have h18 : Reaches bb220 (mkCfgR (some 1) [6, 4] [6, 3, 3, 3, 3, 3, 3, 3, 3, 8, 9]) (mkCfgR (some 1) [2, 2, 2, 2, 2, 2, 2, 2, 2] [2, 3, 8, 9]) 15 := rfl
  have h19 : Reaches bb220 (mkCfgR (some 1) [2, 2, 2, 2, 2, 2, 2, 2, 2] [2, 3, 8, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 3, 3, 3, 8, 9]) 15 := rfl
  have h20 : Reaches bb220 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 3, 3, 3, 8, 9]) (B2cfg 10 0 [8, 9]) 7 := rfl
  have acc := h1
  have acc := reaches_trans acc h2
  have acc := reaches_trans acc h3
  have acc := reaches_trans acc h4
  have acc := reaches_trans acc h5
  have acc := reaches_trans acc h6
  have acc := reaches_trans acc h7
  have acc := reaches_trans acc h8
  have acc := reaches_trans acc h9
  have acc := reaches_trans acc h10
  have acc := reaches_trans acc h11
  have acc := reaches_trans acc h12
  have acc := reaches_trans acc h13
  have acc := reaches_trans acc h14
  have acc := reaches_trans acc h15
  have acc := reaches_trans acc h16
  have acc := reaches_trans acc h17
  have acc := reaches_trans acc h18
  have acc := reaches_trans acc h19
  have acc := reaches_trans acc h20
  exact acc

theorem bb220_halts_gt_f_omega_f10_2 :
    ValidTM 2 20 bb220 ∧ ∃ s, HaltsIn bb220 initConfig s ∧ f_omega (fFin 10 2) < s := by
  refine ⟨bb220_valid, ?_⟩
  have hboot := bb220_bootstrap
  obtain ⟨m, hm⟩ : ∃ m, m = Kfn 10 0 := ⟨_, rfl⟩
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb220_core 10 0 [9]
  rw [← hm] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb220_core (w' := 18) rfl rfl rfl 10 m
  rw [(by omega : 2 * m + 10 + 1 = 2 * m + 11)] at h2
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb220_core (s := 19) (w' := 17) rfl rfl (2 * m + 11) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 11) + 1 = 2 * m + 12)] at h3
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb220_core (s := 18) (w' := 16) rfl rfl (2 * m + 12) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 12) + 1 = 2 * m + 13)] at h4
  obtain ⟨t5, h5, _⟩ := kropitz2_reload_gen bb220_core (s := 17) (w' := 15) rfl rfl (2 * m + 13) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 13) + 1 = 2 * m + 14)] at h5
  obtain ⟨t6, h6, _⟩ := kropitz2_reload_gen bb220_core (s := 16) (w' := 14) rfl rfl (2 * m + 14) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 14) + 1 = 2 * m + 15)] at h6
  obtain ⟨t7, h7, _⟩ := kropitz2_reload_gen bb220_core (s := 15) (w' := 13) rfl rfl (2 * m + 15) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 15) + 1 = 2 * m + 16)] at h7
  obtain ⟨t8, h8, _⟩ := kropitz2_reload_gen bb220_core (s := 14) (w' := 12) rfl rfl (2 * m + 16) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 16) + 1 = 2 * m + 17)] at h8
  obtain ⟨t9, h9, _⟩ := kropitz2_reload_gen bb220_core (s := 13) (w' := 11) rfl rfl (2 * m + 17) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 17) + 1 = 2 * m + 18)] at h9
  obtain ⟨t10, h10, _⟩ := kropitz2_reload_gen bb220_core (s := 12) (w' := 10) rfl rfl (2 * m + 18) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 18) + 1 = 2 * m + 19)] at h10
  obtain ⟨t11, h11, _⟩ := kropitz2_reload_gen bb220_core (s := 11) (w' := 6) rfl rfl (2 * m + 19) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 19) + 1 = 2 * m + 20)] at h11
  obtain ⟨t12, h12, _⟩ := kropitz2_reload_gen bb220_core (s := 7) (w' := 7) rfl rfl (2 * m + 20) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 20) + 1 = 2 * m + 21)] at h12
  obtain ⟨t13, h13, hle13⟩ := kropitz2_step_8 bb220_core (2 * m + 21) 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb220_core rfl rfl (2 * m + 21) (Kfn (2 * m + 21) 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 (reaches_trans h8 (reaches_trans h9 (reaches_trans h10 (reaches_trans h11 (reaches_trans h12 (reaches_trans h13 (hhalt))))))))))))))
  have hfk : fFin 10 2 < Kfn 10 0 := Kfn_zero_gt_fFin2 10 (by omega)
  have hmono : f_omega (fFin 10 2) ≤ f_omega (2 * m + 20) :=
    (fOmegaMul_props 1 0).mono _ _ (by omega)
  have hgt : f_omega (2 * m + 20) < Kfn (2 * m + 21) 0 :=
    Kfn_zero_gt_fOmega (2 * m + 20)
  exact ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hgt (by omega))⟩

#print axioms bb220_halts_gt_f_omega_f10_2

end BB2_20
end BB
