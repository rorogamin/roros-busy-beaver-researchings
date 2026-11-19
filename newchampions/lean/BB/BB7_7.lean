/-
  BB/BB7_7.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 7):
    TM: 6LF3LB6LA2RA4LB5RC5LA_1RZ3RB1LD2RA3LF5RB6LD_3RB1LB3LC2RC4LC1LE5RB_3RB3RE3LC2RC0LE3RD1LA_5RB3RE2LE4LC3LG5LE1RZ_5RB5RB4RF1LF2LD5LF4RG_5LF1RZ5LB1LG2RG5LG1RZ
    Domain: BB(7, 7) (7 states, 7 symbols)
    Previous best dominated bounds: BB(7, 6) > f_{ω^2}(110), BB(6, 7) > f_{ω×2+1}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+1}(3)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_7

def bb77 : TM
  -- State A (0): 6LF 3LB 6LA 2RA 4LB 5RC 5LA
  | 0, 0 => some ⟨6, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨6, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.R, some 2⟩
  | 0, 6 => some ⟨5, Dir.L, some 0⟩
  -- State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨6, Dir.L, some 3⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨5, Dir.R, some 1⟩
  -- State D (3): 3RB 3RE 3LC 2RC 0LE 3RD 1LA
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨0, Dir.L, some 4⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨1, Dir.L, some 0⟩
  -- State E (4): 5RB 3RE 2LE 4LC 3LG 5LE 1RZ
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨1, Dir.R, none⟩
  -- State F (5): 5RB 5RB 4RF 1LF 2LD 5LF 4RG
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨4, Dir.R, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨2, Dir.L, some 3⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨4, Dir.R, some 6⟩
  -- State G (6): 5LF 1RZ 5LB 1LG 2RG 5LG 1RZ
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨1, Dir.R, none⟩
  | 6, 2 => some ⟨5, Dir.L, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 6⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨1, Dir.R, none⟩
  | _, _ => none

theorem bb77_valid : ValidTM 7 7 bb77 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 => simp [bb77]
    | _ + 7, _ => omega
    | _, _ + 7 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 => omega
    | _ + 7, _ => rfl
    | 0, _ + 7 | 1, _ + 7 | 2, _ + 7 | 3, _ + 7 | 4, _ + 7 | 5, _ + 7 | 6, _ + 7 => rfl

theorem bb77_core : Fwp2_7Core bb77 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bb77_bootstrap :
    Reaches bb77 initConfig (Scfg 2 0 0 [2, 2, 2, 2, 1, 5]) 69 := rfl

theorem bb77_halts_gt_f_omega2_plus_1_3 :
    ValidTM 7 7 bb77 ∧ ∃ t, HaltsIn bb77 initConfig t ∧ f_omega2_plus 1 3 < t := by
  refine ⟨bb77_valid, ?_⟩
  have hboot := bb77_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2_7 bb77_core 1 0 [2, 2, 2, 1, 5]
  have hm1_3 : 3 ≤ m1 := Nat.le_trans (by omega : 3 ≤ 17) (Nat.le_trans H2_7_0_ge hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb77_core 3 r1 m1 [1, 5]
  obtain ⟨t3, h3, _⟩ := fwp2_step bb77_core.fp (r2 + 1) 0 m2 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb77_core r2 (Pfn (r2 + 1) 0 m2)
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3) hhalt
  have hlt1 : f_omega2_plus 1 3 < iter H2_7 3 3 :=
    iter_strict_dom H2_7 f_omega2 1 H2_7_gt (fOmega2_props 1 0 0) 3 3 (by omega) (by omega)
  have hlt2 : iter H2_7 3 3 ≤ iter H2_7 3 m1 := iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) 3 hm1_3
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  have hlt_m2 : f_omega2_plus 1 3 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb77_halts_gt_f_omega2_plus_1_3

end BB7_7
end BB
