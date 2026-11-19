/-
  BB/BB2_12.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(2, 12):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA11RA7LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ11LB11LB
    Domain: BB(2, 12) (2 states, 12 symbols)
    Previous best dominated bound: our BB(2, 11) > f_7(2)
    Proved bound here: halts from blank tape in exact s steps with s > f_{17}(2)
-/

import BB.TM
import BB.FGH
import BB.Kropitz2

namespace BB
namespace BB2_12

/-- The 2-state, 12-symbol Turing machine `bb212`. -/
def bb212 : TM
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
  | 0, 10 => some ⟨11, Dir.R, some 0⟩
  | 0, 11 => some ⟨7,  Dir.L, some 1⟩
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
  | 1, 10 => some ⟨11, Dir.L, some 1⟩
  | 1, 11 => some ⟨11, Dir.L, some 1⟩
  | _, _  => none

/-- Certificate that `bb212` is a valid 2-state, 12-symbol Turing machine. -/
theorem bb212_valid : ValidTM 2 12 bb212 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => simp [bb212]
      | _ + 12 => omega
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => simp [bb212]
      | _ + 12 => omega
    | _ + 2 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
      | _ + 12 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
      | _ + 12 => rfl
    | _ + 2 => rfl

theorem bb212_core : Kropitz2Core bb212 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bootstrap from blank tape to `B2cfg 2 0 [8, 9]` in 36 steps (`20 + 16`). -/
theorem bb212_bootstrap :
    Reaches bb212 initConfig (B2cfg 2 0 [8, 9]) 36 := by
  have h1 : Reaches bb212 initConfig (mkCfgR (some 0) [4] [3, 3, 7, 9]) 20 := rfl
  have h2 : Reaches bb212 (mkCfgR (some 0) [4] [3, 3, 7, 9]) (B2cfg 2 0 [8, 9]) 16 := rfl
  exact reaches_trans h1 h2

/-- Main Champion Theorem for BB(2, 12): `bb212` halts with strictly more than `f_{17}(2)` steps. -/
theorem bb212_halts_gt_f_17_2 :
    ValidTM 2 12 bb212 ∧ ∃ s, HaltsIn bb212 initConfig s ∧ fFin 17 2 < s := by
  refine ⟨bb212_valid, ?_⟩
  have hboot := bb212_bootstrap
  obtain ⟨t1, h1, _⟩ := kropitz2_step_8 bb212_core 2 0 [9]
  rw [Kfn_2_0_eq] at h1
  obtain ⟨t2, h2, _⟩ := kropitz2_pass2_reload bb212_core (w' := 10) rfl rfl rfl 2 6
  obtain ⟨t3, h3, _⟩ := kropitz2_reload_gen bb212_core (s := 11) (w' := 6) rfl rfl 15 0 []
  obtain ⟨t4, h4, _⟩ := kropitz2_reload_gen bb212_core (s := 7) (w' := 7) rfl rfl 16 0 []
  obtain ⟨t5, h5, hle5⟩ := kropitz2_step_8 bb212_core 17 0 []
  obtain ⟨cf, hhalt, hst⟩ := kropitz2_halt bb212_core rfl rfl 17 (Kfn 17 0)
  have hreach := reaches_trans hboot (reaches_trans h1 (reaches_trans h2
    (reaches_trans h3 (reaches_trans h4 (reaches_trans h5 hhalt)))))
  have hbound : fFin 17 2 < Kfn 17 0 := Kfn_zero_gt_fFin2 17 (by omega)
  exact ⟨_, ⟨cf, hreach, hst⟩, by omega⟩

#print axioms bb212_halts_gt_f_17_2

end BB2_12
end BB
