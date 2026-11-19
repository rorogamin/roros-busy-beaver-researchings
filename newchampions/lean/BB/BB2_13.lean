/-
  BB/BB2_13.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 13):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA12RA7LB11LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ12LB11LB12LB
    Domain: BB(2, 13) (2 states, 13 symbols)
    Previous best dominated bound: our BB(2, 12) > f_{17}(2)
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(2^16)
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_13

/-- The 2-state, 13-symbol Turing machine `bb213`. -/
def bb213 : TM
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
  | 0, 10 => some ⟨12, Dir.R, some 0⟩
  | 0, 11 => some ⟨7,  Dir.L, some 1⟩
  | 0, 12 => some ⟨11, Dir.L, some 1⟩
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
  | 1, 10 => some ⟨12, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | 1, 12 => some ⟨12, Dir.L, some 1⟩
  | _, _  => none

/-- Certificate that `bb213` is a valid 2-state, 13-symbol Turing machine. -/
theorem bb213_valid : ValidTM 2 13 bb213 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => simp [bb213]
      | _ + 13 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => simp [bb213]
      | _ + 13 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => omega
      | _ + 13 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => omega
      | _ + 13 => rfl
    | _ + 2 => rfl

theorem bb213_core : Kropitz2Core bb213 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bootstrap from blank tape to `B2cfg 3 0 [8, 9]` in 54 steps (`20 + 20 + 14`). -/
theorem bb213_bootstrap :
    Reaches bb213 initConfig (B2cfg 3 0 [8, 9]) 54 := by
  have h1 : Reaches bb213 initConfig (mkCfgR (some 0) [4] [3, 3, 11, 9]) 20 := rfl
  have h2 : Reaches bb213 (mkCfgR (some 0) [4] [3, 3, 11, 9])
                          (mkCfgR (some 1) [] [4, 3, 3, 3, 8, 9]) 20 := rfl
  have h3 : Reaches bb213 (mkCfgR (some 1) [] [4, 3, 3, 3, 8, 9]) (B2cfg 3 0 [8, 9]) 14 := rfl
  exact reaches_trans h1 (reaches_trans h2 h3)

/-- Main Champion Theorem for BB(2, 13): `bb213` halts with strictly more than `f_ω(2^16)` steps. -/
theorem bb213_halts_gt_f_omega_2_16 :
    ValidTM 2 13 bb213 ∧ ∃ s, HaltsIn bb213 initConfig s ∧ f_omega (2 ^ 16) < s := by
  refine ⟨bb213_valid, ?_⟩
  have hboot := bb213_bootstrap
  obtain ⟨m, hm⟩ : ∃ m, m = Kfn 3 0 := ⟨_, rfl⟩
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb213_core 3 0 [9]
  rw [← hm] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb213_core (w' := 11) rfl rfl rfl 3 m
  rw [(by omega : 2 * m + 3 + 1 = 2 * m + 4)] at h2
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb213_core (s := 12) (w' := 10) rfl rfl (2 * m + 4) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 4) + 1 = 2 * m + 5)] at h3
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb213_core (s := 11) (w' := 6) rfl rfl (2 * m + 5) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 5) + 1 = 2 * m + 6)] at h4
  obtain ⟨t5, h5, _⟩ := kropitz2_reload_gen bb213_core (s := 7) (w' := 7) rfl rfl (2 * m + 6) 0 []
  rw [(by omega : 2 * 0 + (2 * m + 6) + 1 = 2 * m + 7)] at h5
  obtain ⟨t6, h6, hle6⟩ := kropitz2_step_8 bb213_core (2 * m + 7) 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb213_core rfl rfl (2 * m + 7) (Kfn (2 * m + 7) 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2
    (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 hhalt))))))
  have hpow15 := Kfn_3_0_pow
  have hpow16 : 2 ^ 16 = 2 * 2 ^ 15 := rfl
  have hle_arg : 2 ^ 16 ≤ 2 * m + 6 := by omega
  have hmono : f_omega (2 ^ 16) ≤ f_omega (2 * m + 6) :=
    (fOmegaMul_props 1 0).mono _ _ hle_arg
  have hgt : f_omega (2 * m + 6) < Kfn (2 * m + 7) 0 :=
    Kfn_zero_gt_fOmega (2 * m + 6)
  exact ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hgt (by omega))⟩

#print axioms bb213_halts_gt_f_omega_2_16

end BB2_13
end BB
