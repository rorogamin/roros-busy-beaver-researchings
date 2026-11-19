/-
  BB/BB2_11.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 11):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA7RA_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ7LB
    Domain: BB(2, 11) (2 states, 11 symbols)
    Previous best dominated bound: BB(2, 9) > 10↑↑10↑↑10↑↑10↑↑10↑↑155 (< f_4(3) < f_5(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_7(2)
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_11

/-- The 2-state, 11-symbol Turing machine `bb211`. -/
def bb211 : TM
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
  | 0, 10 => some ⟨7,  Dir.R, some 0⟩
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
  | 1, 10 => some ⟨7,  Dir.L, some 1⟩
  | _, _  => none

/-- Certificate that `bb211` is a valid 2-state, 11-symbol Turing machine. -/
theorem bb211_valid : ValidTM 2 11 bb211 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => simp [bb211]
      | _ + 11 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => simp [bb211]
      | _ + 11 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => omega
      | _ + 11 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => omega
      | _ + 11 => rfl
    | _ + 2 => rfl

theorem bb211_core : Kropitz2Core bb211 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bootstrap from blank tape to `B2cfg 7 0 [8]` in 179 steps, split into `<= 25`-step chunks. -/
theorem bb211_bootstrap :
    Reaches bb211 initConfig (B2cfg 7 0 [8]) 179 := by
  have h1 : Reaches bb211 initConfig (mkCfgR (some 0) [6, 4] [2, 3, 9]) 25 := rfl
  have h2 : Reaches bb211 (mkCfgR (some 0) [6, 4] [2, 3, 9])
                          (mkCfgR (some 0) [4, 3, 3] [6, 5, 3, 9]) 25 := rfl
  have h3 : Reaches bb211 (mkCfgR (some 0) [4, 3, 3] [6, 5, 3, 9])
                          (mkCfgR (some 0) [4, 3, 3, 3, 3] [3, 3, 9]) 25 := rfl
  have h4 : Reaches bb211 (mkCfgR (some 0) [4, 3, 3, 3, 3] [3, 3, 9])
                          (mkCfgR (some 1) [2, 2, 3, 3] [3, 3, 3, 7]) 25 := rfl
  have h5 : Reaches bb211 (mkCfgR (some 1) [2, 2, 3, 3] [3, 3, 3, 7])
                          (mkCfgR (some 1) [2, 2, 2] [3, 3, 3, 3, 7]) 25 := rfl
  have h6 : Reaches bb211 (mkCfgR (some 1) [2, 2, 2] [3, 3, 3, 3, 7])
                          (mkCfgR (some 1) [6, 6, 4] [6, 3, 3, 3, 3, 8]) 25 := rfl
  have h7 : Reaches bb211 (mkCfgR (some 1) [6, 6, 4] [6, 3, 3, 3, 3, 8])
                          (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 8]) 25 := rfl
  have h8 : Reaches bb211 (mkCfgR (some 0) [6, 6, 6, 6, 4] [3, 3, 3, 3, 8])
                          (B2cfg 7 0 [8]) 4 := rfl
  exact reaches_trans h1 (reaches_trans h2 (reaches_trans h3 (reaches_trans h4
    (reaches_trans h5 (reaches_trans h6 (reaches_trans h7 h8))))))

/-- Main Champion Theorem for BB(2, 11): `bb211` halts with strictly more than `f_7(2)` steps. -/
theorem bb211_halts_gt_f_7_2 :
    ValidTM 2 11 bb211 ∧ ∃ s, HaltsIn bb211 initConfig s ∧ fFin 7 2 < s := by
  refine ⟨bb211_valid, ?_⟩
  have hboot := bb211_bootstrap
  obtain ⟨t1, h1, hle1⟩ := kropitz2_step_8 bb211_core 7 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb211_core rfl rfl 7 (Kfn 7 0)
  have hreach : Reaches bb211 initConfig cf (179 + t1 + (2 * 7 + 5)) :=
    reaches_trans (reaches_trans hboot h1) hhalt
  have hbound : fFin 7 2 < Kfn 7 0 := Kfn_zero_gt_fFin2 7 (by omega)
  exact ⟨_, ⟨cf, hreach, hst⟩, by omega⟩

#print axioms bb211_halts_gt_f_7_2

end BB2_11
end BB
