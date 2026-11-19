/-
  BB/BB7_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 6):
    TM: 1LE3LB2LF2RA4LB2RA_4LF3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC1RZ3RD_5RB3RE1RZ4LC3LG5LE_5RB4RF1LF1LF2LF5RG_5LF5RG1LA1LG1RD5LG
    Domain: BB(7, 6) (7 states, 6 symbols)
    Previous wiki champion: BB(7, 6) > f_{ω^2}(110) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+1}(2)
    (strictly beats f_{ω^2}(110) by a full FGH ordinal level, and strictly < our BB(7, 7) & BB(8, 6))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_6

def bb76 : TM
  -- State A (0): 1LE 3LB 2LF 2RA 4LB 2RA
  | 0, 0 => some ⟨1, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  -- State B (1): 4LF 3RB 1LD 2RA 3LF 5RB
  | 1, 0 => some ⟨4, Dir.L, some 5⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  -- State D (3): 3RB 3RE 3LC 2RC 1RZ 3RD
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.R, none⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  -- State E (4): 5RB 3RE 1RZ 4LC 3LG 5LE
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.R, none⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  -- State F (5): 5RB 4RF 1LF 1LF 2LF 5RG
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨4, Dir.R, some 5⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨2, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.R, some 6⟩
  -- State G (6): 5LF 5RG 1LA 1LG 1RD 5LG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨5, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 0⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨1, Dir.R, some 3⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | _, _ => none

theorem bb76_valid : ValidTM 7 6 bb76 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 7 => rfl

theorem bb76_fp : Fwp2Core bb76 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb76 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb76 _
  | succ k ih =>
    have h1 : step bb76 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb76 k _ _ _ h1 h2

private theorem loop_G1 (n : Nat) (L R : List Nat) :
    Reaches bb76 (mkCfgR (some 6) L (rep n 1 R))
                 (mkCfgR (some 6) (rep n 5 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb76 _
  | succ k ih =>
    have h1 : step bb76 (mkCfgR (some 6) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 6) (5 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb76) (q := 6) (w := 4) (cur := 1) rfl
    have h2 := ih (5 :: L); rw [rep_snoc_one] at h2; exact steps_succ bb76 k _ _ _ h1 h2

private theorem rep_add (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem reload_2 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb76 (Scfg (r + 1) 0 m (2 :: R))
                      (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) t := by
  have h1 : step bb76 (Scfg (r + 1) 0 m (2 :: R)) =
            some (mkCfgR (some 5) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 0) (w := 1) (cur := 2) rfl
  have h2 : step bb76 (mkCfgR (some 5) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) =
            some (mkCfgR (some 5) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 1 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 2) rfl
  have h3 := loop_F3 (2 * m) (rep (r + 1) 5 []) (1 :: 2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb76 (mkCfgR (some 5) (5 :: rep r 5 []) (3 :: rep (2 * m + 1) 1 (2 :: R))) =
            some (mkCfgR (some 5) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (2 :: R))) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 3) rfl
  have h5 : step bb76 (mkCfgR (some 5) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (2 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 2) 1 (2 :: R))) :=
    step_mkCfgR_R (tm := bb76) (q := 5) (w := 4) (cur := 5) rfl
  have h6 := loop_G1 (2 * m + 2) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_add] at h6
  have heq : (2 * m + 2) + (r + 1) = (r + 2 * m + 2) + 1 := by omega
  rw [heq] at h6
  have h7 : step bb76 (mkCfgR (some 6) (5 :: rep (r + 2 * m + 2) 5 []) (2 :: R)) =
            some (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (5 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 6) (w := 0) (cur := 2) rfl
  have h8 : step bb76 (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (5 :: 1 :: R)) =
            some (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) :=
    step_mkCfgR_R (tm := bb76) (q := 0) (w := 1) (cur := 5) rfl
  exact ⟨_, reaches_trans
    (steps_succ bb76 _ _ _ _ h1 (steps_succ bb76 _ _ _ _ h2 h3))
    (steps_succ bb76 _ _ _ _ h4 (steps_succ bb76 _ _ _ _ h5 (reaches_trans h6
      (steps_succ bb76 _ _ _ _ h7 (steps_one bb76 _ _ h8)))))⟩

theorem rule_2 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb76 (Scfg (r + 1) 0 m (2 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H2_7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 r m R
  obtain ⟨t2, h2, hle2⟩ := fwp2_empty3 bb76_fp (r + 2 * m + 1) R
  exact ⟨r + 2 * m + 1, Pempty (r + 2 * m + 1), t1 + t2, reaches_trans h1 h2,
    Pempty_mono (by omega), Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb76_bootstrap :
    Reaches bb76 initConfig (Scfg 1 0 3 [2, 2]) 112 := rfl

theorem bb76_halts_gt_f_omega2_plus_1_2 :
    ValidTM 7 6 bb76 ∧ ∃ t, HaltsIn bb76 initConfig t ∧ f_omega2_plus 1 2 < t := by
  refine ⟨bb76_valid, ?_⟩
  have hboot := bb76_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2 0 3 [2]
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2 r1 m1 []
  have hh1 : step bb76 (Scfg (r2 + 1) 0 m2 []) =
             some (mkCfgR (some 4) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 1]) := rfl
  have hh2 : step bb76 (mkCfgR (some 4) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 1]) =
             some (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [1]) :=
    step_mkCfgR_R (tm := bb76) (q := 4) (w := 0) (cur := 2) rfl
  have hhalt : Reaches bb76 (Scfg (r2 + 1) 0 m2 [])
      (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [1]) 2 :=
    steps_succ bb76 1 _ _ _ hh1 (steps_one bb76 _ _ hh2)
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2 2 < m1 :=
    Nat.lt_of_lt_of_le (H2_7_gt 2 (by omega)) (Nat.le_trans (H2_7_mono (by omega : 2 ≤ 3)) hm1)
  have hlt2 : f_omega2 (f_omega2 2) ≤ f_omega2 m1 :=
    (fOmega2_props 1 0 0).mono _ _ (Nat.le_of_lt hlt1)
  have hlt3 : f_omega2 m1 < m2 :=
    Nat.lt_of_lt_of_le (H2_7_gt m1 (by omega)) hm2
  have hdef : f_omega2_plus 1 2 = f_omega2 (f_omega2 2) := by
    change iter f_omega2 2 2 = f_omega2 (f_omega2 2)
    rw [iter_succ, iter_succ, iter_zero]
  have hlt_m2 : f_omega2_plus 1 2 < m2 := by rw [hdef]; exact Nat.lt_of_le_of_lt hlt2 hlt3
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans ht2 (by omega))⟩

#print axioms bb76_halts_gt_f_omega2_plus_1_2

end BB7_6
end BB
