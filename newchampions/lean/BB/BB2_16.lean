/-
  BB/BB2_16.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 16):
    Domain: BB(2, 16) (2 states, 16 symbols)
    Previous best dominated bound: our BB(2, 15) > f_ω(f_5(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_6(2))
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_16

def bb216 : TM
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
  | 0, 10 => some ⟨15, Dir.R, some 0⟩
  | 0, 11 => some ⟨7, Dir.L, some 1⟩
  | 0, 12 => some ⟨11, Dir.L, some 1⟩
  | 0, 13 => some ⟨12, Dir.L, some 1⟩
  | 0, 14 => some ⟨13, Dir.L, some 1⟩
  | 0, 15 => some ⟨14, Dir.L, some 1⟩
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
  | 1, 10 => some ⟨15, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | 1, 12 => some ⟨12, Dir.L, some 1⟩
  | 1, 13 => some ⟨13, Dir.L, some 1⟩
  | 1, 14 => some ⟨14, Dir.L, some 1⟩
  | 1, 15 => some ⟨15, Dir.L, some 1⟩
  | _, _  => none

theorem bb216_valid : ValidTM 2 16 bb216 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => simp [bb216]
      | _ + 16 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => simp [bb216]
      | _ + 16 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => omega
      | _ + 16 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => omega
      | _ + 16 => rfl
    | _ + 2 => rfl

theorem bb216_core : Kropitz2Core bb216 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bb216_bootstrap :
    Reaches bb216 initConfig (B2cfg 6 0 [8, 9]) 132 := by
  have h1 : Reaches bb216 initConfig (mkCfgR (some 1) [] [4, 3, 3, 13, 9]) 25 := rfl
  have h2 : Reaches bb216 (mkCfgR (some 1) [] [4, 3, 3, 13, 9]) (mkCfgR (some 0) [4] [3, 3, 3, 3, 12, 9]) 25 := rfl
  have h3 : Reaches bb216 (mkCfgR (some 0) [4] [3, 3, 3, 3, 12, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 11, 9]) 25 := rfl
  have h4 : Reaches bb216 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 11, 9]) (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 7, 9]) 25 := rfl
  have h5 : Reaches bb216 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 7, 9]) (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 8, 9]) 25 := rfl
  have h6 : Reaches bb216 (mkCfgR (some 0) [4] [3, 3, 3, 3, 3, 3, 3, 8, 9]) (B2cfg 6 0 [8, 9]) 7 := rfl
  exact reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (h6)))))

theorem bb216_halts_gt_f_omega_f6_2 :
    ValidTM 2 16 bb216 ∧ ∃ s, HaltsIn bb216 initConfig s ∧ f_omega (fFin 6 2) < s := by
  refine ⟨bb216_valid, ?_⟩
  have hboot := bb216_bootstrap
  obtain ⟨m, hm⟩ : ∃ m, m = Kfn 6 0 := ⟨_, rfl⟩
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb216_core 6 0 [9]
  rw [← hm] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb216_core (w' := 14) rfl rfl rfl 6 m
  rw [(by omega : 2 * m + 6 + 1 = 2 * m + 7)] at h2
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb216_core (s := 15) (w' := 13) rfl rfl (2 * m + 7) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 7) + 1 = 2 * m + 8)] at h3
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb216_core (s := 14) (w' := 12) rfl rfl (2 * m + 8) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 8) + 1 = 2 * m + 9)] at h4
  obtain ⟨t5, h5, _⟩ := kropitz2_reload_gen bb216_core (s := 13) (w' := 11) rfl rfl (2 * m + 9) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 9) + 1 = 2 * m + 10)] at h5
  obtain ⟨t6, h6, _⟩ := kropitz2_reload_gen bb216_core (s := 12) (w' := 10) rfl rfl (2 * m + 10) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 10) + 1 = 2 * m + 11)] at h6
  obtain ⟨t7, h7, _⟩ := kropitz2_reload_gen bb216_core (s := 11) (w' := 6) rfl rfl (2 * m + 11) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 11) + 1 = 2 * m + 12)] at h7
  obtain ⟨t8, h8, _⟩ := kropitz2_reload_gen bb216_core (s := 7) (w' := 7) rfl rfl (2 * m + 12) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 12) + 1 = 2 * m + 13)] at h8
  obtain ⟨t9, h9, hle9⟩ := kropitz2_step_8 bb216_core (2 * m + 13) 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb216_core rfl rfl (2 * m + 13) (Kfn (2 * m + 13) 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 (reaches_trans h8 (reaches_trans h9 (hhalt))))))))))
  have hfk : fFin 6 2 < Kfn 6 0 := Kfn_zero_gt_fFin2 6 (by omega)
  have hmono : f_omega (fFin 6 2) ≤ f_omega (2 * m + 12) :=
    (fOmegaMul_props 1 0).mono _ _ (by omega)
  have hgt : f_omega (2 * m + 12) < Kfn (2 * m + 13) 0 :=
    Kfn_zero_gt_fOmega (2 * m + 12)
  exact ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hgt (by omega))⟩

#print axioms bb216_halts_gt_f_omega_f6_2

end BB2_16
end BB
