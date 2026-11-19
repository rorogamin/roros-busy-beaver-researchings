/-
  BB/BB2_14.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 14):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA13RA7LB11LB12LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ13LB11LB12LB13LB
    Domain: BB(2, 14) (2 states, 14 symbols)
    Previous best dominated bound: our BB(2, 13) > f_ω(2^16)
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_4(2))
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_14

/-- The 2-state, 14-symbol Turing machine `bb214`. -/
def bb214 : TM
  -- State A (0)
  | 0, 0  => some ⟨9,  Dir.L, some 1⟩
  | 0, 1  => some ⟨5,  Dir.L, some 0⟩
  | 0, 2  => some ⟨1,  Dir.L, some 1⟩
  | 0, 3  => some ⟨6,  Dir.R, some 0⟩
  | 0, 4  => some ⟨3,  Dir.R, some 0⟩
  | 0, 5  => some ⟨4,  Dir.R, some 0⟩
  | 0, 6  => some ⟨2,  Dir.R, some 1⟩
  | 0, 7  => some ⟨8,  Dir.L, some 1⟩
  | 0, 8  => some ⟨5,  Dir.L, some 0⟩
  | 0, 9  => some ⟨10, Dir.L, some 0⟩
  | 0, 10 => some ⟨13, Dir.R, some 0⟩
  | 0, 11 => some ⟨7,  Dir.L, some 1⟩
  | 0, 12 => some ⟨11, Dir.L, some 1⟩
  | 0, 13 => some ⟨12, Dir.L, some 1⟩
  -- State B (1)
  | 1, 0  => some ⟨4,  Dir.R, some 0⟩
  | 1, 1  => some ⟨1,  Dir.L, some 0⟩
  | 1, 2  => some ⟨3,  Dir.L, some 1⟩
  | 1, 3  => some ⟨2,  Dir.R, some 1⟩
  | 1, 4  => some ⟨2,  Dir.R, some 1⟩
  | 1, 5  => some ⟨3,  Dir.L, some 0⟩
  | 1, 6  => some ⟨3,  Dir.L, some 1⟩
  | 1, 7  => some ⟨7,  Dir.L, some 1⟩
  | 1, 8  => some ⟨8,  Dir.L, some 1⟩
  | 1, 9  => some ⟨1,  Dir.R, none⟩
  | 1, 10 => some ⟨13, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | 1, 12 => some ⟨12, Dir.L, some 1⟩
  | 1, 13 => some ⟨13, Dir.L, some 1⟩
  | _, _  => none

/-- Certificate that `bb214` is a valid 2-state, 14-symbol Turing machine. -/
theorem bb214_valid : ValidTM 2 14 bb214 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => simp [bb214]
      | _ + 14 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => simp [bb214]
      | _ + 14 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => omega
      | _ + 14 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => omega
      | _ + 14 => rfl
    | _ + 2 => rfl

theorem bb214_core : Kropitz2Core bb214 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bootstrap from blank tape to `B2cfg 4 0 [8, 9]` in 76 steps (`20 + 20 + 20 + 16`). -/
theorem bb214_bootstrap :
    Reaches bb214 initConfig (B2cfg 4 0 [8, 9]) 76 := by
  have h1 : Reaches bb214 initConfig (mkCfgR (some 0) [4] [3, 3, 12, 9]) 20 := rfl
  have h2 : Reaches bb214 (mkCfgR (some 0) [4] [3, 3, 12, 9])
                          (mkCfgR (some 1) [] [4, 3, 3, 3, 7, 9]) 20 := rfl
  have h3 : Reaches bb214 (mkCfgR (some 1) [] [4, 3, 3, 3, 7, 9])
                          (mkCfgR (some 1) [2] [3, 3, 3, 3, 8, 9]) 20 := rfl
  have h4 : Reaches bb214 (mkCfgR (some 1) [2] [3, 3, 3, 3, 8, 9]) (B2cfg 4 0 [8, 9]) 16 := rfl
  exact reaches_trans h1 (reaches_trans h2 (reaches_trans h3 h4))

/-- Main Champion Theorem for BB(2, 14): `bb214` halts with strictly more than `f_ω(f_4(2))` steps. -/
theorem bb214_halts_gt_f_omega_f4_2 :
    ValidTM 2 14 bb214 ∧ ∃ s, HaltsIn bb214 initConfig s ∧ f_omega (fFin 4 2) < s := by
  refine ⟨bb214_valid, ?_⟩
  have hboot := bb214_bootstrap
  obtain ⟨m, hm⟩ : ∃ m, m = Kfn 4 0 := ⟨_, rfl⟩
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb214_core 4 0 [9]
  rw [← hm] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb214_core (w' := 12) rfl rfl rfl 4 m
  rw [(by omega : 2 * m + 4 + 1 = 2 * m + 5)] at h2
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb214_core (s := 13) (w' := 11) rfl rfl (2 * m + 5) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 5) + 1 = 2 * m + 6)] at h3
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb214_core (s := 12) (w' := 10) rfl rfl (2 * m + 6) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 6) + 1 = 2 * m + 7)] at h4
  obtain ⟨t5, h5, _⟩ := kropitz2_reload_gen bb214_core (s := 11) (w' := 6) rfl rfl (2 * m + 7) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 7) + 1 = 2 * m + 8)] at h5
  obtain ⟨t6, h6, _⟩ := kropitz2_reload_gen bb214_core (s := 7) (w' := 7) rfl rfl (2 * m + 8) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 8) + 1 = 2 * m + 9)] at h6
  obtain ⟨t7, h7, hle7⟩ := kropitz2_step_8 bb214_core (2 * m + 9) 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb214_core rfl rfl (2 * m + 9) (Kfn (2 * m + 9) 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2
    (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 hhalt)))))))
  have hf4 : fFin 4 2 < Kfn 4 0 := Kfn_zero_gt_fFin2 4 (by omega)
  have hmono : f_omega (fFin 4 2) ≤ f_omega (2 * m + 8) :=
    (fOmegaMul_props 1 0).mono _ _ (by omega)
  have hgt : f_omega (2 * m + 8) < Kfn (2 * m + 9) 0 :=
    Kfn_zero_gt_fOmega (2 * m + 8)
  exact ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hgt (by omega))⟩

#print axioms bb214_halts_gt_f_omega_f4_2

end BB2_14
end BB
