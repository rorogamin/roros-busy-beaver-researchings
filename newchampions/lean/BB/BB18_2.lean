/-
  BB/BB18_2.lean
  18-state, 2-symbol Busy Beaver champion:
    ValidTM 18 2 bb18_2  ∧  ∃ s, HaltsIn bb18_2 initConfig s ∧ iter f_omega_mul2 2 (fFin 5 2) < s
  Strictly beats the bbchallenge wiki BB(18) champion (> f_{ω×2}(f_{ω+1}(f_4(2)))).

  Uses the shared 15-state Jacobzheng f_{ω×2} engine (BB/Jacobzheng.lean)
  with exit transitions J0=1LQ, K0=1RZ, L0=1LH.
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.JZMath
import BB.Jacobzheng

namespace BB

def bb18_2 : TM := fun s sym =>
  match s, sym with
  | 0,  0 => some ⟨1, Dir.L, some 1⟩   -- A0: 1LB
  | 0,  1 => some ⟨0, Dir.L, some 12⟩  -- A1: 0LM
  | 1,  0 => some ⟨1, Dir.R, some 2⟩   -- B0: 1RC
  | 1,  1 => some ⟨1, Dir.R, some 13⟩  -- B1: 1RN
  | 2,  0 => some ⟨1, Dir.R, some 3⟩   -- C0: 1RD
  | 2,  1 => some ⟨1, Dir.R, some 2⟩   -- C1: 1RC
  | 3,  0 => some ⟨0, Dir.L, some 4⟩   -- D0: 0LE
  | 3,  1 => some ⟨1, Dir.R, some 16⟩  -- D1: 1RQ
  | 4,  0 => some ⟨1, Dir.L, some 5⟩   -- E0: 1LF
  | 4,  1 => some ⟨1, Dir.L, some 4⟩   -- E1: 1LE
  | 5,  0 => some ⟨0, Dir.L, some 6⟩   -- F0: 0LG
  | 5,  1 => some ⟨1, Dir.L, some 4⟩   -- F1: 1LE
  | 6,  0 => some ⟨1, Dir.R, some 7⟩   -- G0: 1RH
  | 6,  1 => some ⟨1, Dir.R, some 8⟩   -- G1: 1RI
  | 7,  0 => some ⟨0, Dir.R, some 7⟩   -- H0: 0RH
  | 7,  1 => some ⟨0, Dir.R, some 2⟩   -- H1: 0RC
  | 8,  0 => some ⟨0, Dir.R, some 9⟩   -- I0: 0RJ
  | 8,  1 => some ⟨1, Dir.R, some 7⟩   -- I1: 1RH
  | 9,  0 => some ⟨1, Dir.L, some 16⟩  -- J0: 1LQ
  | 9,  1 => some ⟨0, Dir.R, some 10⟩  -- J1: 0RK
  | 10, 0 => some ⟨1, Dir.R, none⟩     -- K0: 1RZ
  | 10, 1 => some ⟨1, Dir.R, some 11⟩  -- K1: 1RL
  | 11, 0 => some ⟨1, Dir.L, some 7⟩   -- L0: 1LH
  | 11, 1 => some ⟨1, Dir.R, some 9⟩   -- L1: 1RJ
  | 12, 0 => some ⟨1, Dir.L, some 0⟩   -- M0: 1LA
  | 12, 1 => some ⟨1, Dir.L, some 12⟩  -- M1: 1LM
  | 13, 0 => some ⟨0, Dir.L, some 0⟩   -- N0: 0LA
  | 13, 1 => some ⟨0, Dir.R, some 14⟩  -- N1: 0RO
  | 14, 0 => some ⟨0, Dir.L, some 2⟩   -- O0: 0LC
  | 14, 1 => some ⟨1, Dir.R, some 15⟩  -- O1: 1RP
  | 15, 0 => some ⟨0, Dir.L, some 0⟩   -- P0: 0LA
  | 15, 1 => some ⟨1, Dir.R, some 13⟩  -- P1: 1RN
  | 16, 0 => some ⟨0, Dir.L, some 17⟩  -- Q0: 0LR
  | 16, 1 => some ⟨1, Dir.L, some 0⟩   -- Q1: 1LA
  | 17, 0 => some ⟨0, Dir.R, some 8⟩   -- R0: 0RI
  | 17, 1 => some ⟨1, Dir.L, some 17⟩  -- R1: 1LR
  | _,  _ => none

theorem bb18_2_valid : ValidTM 18 2 bb18_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 =>
      match sym with
      | 0 | 1 => simp [bb18_2]
      | _ + 2 => omega
    | _ + 18 => omega
  · intro s sym h
    match s with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 =>
      match sym with
      | 0 | 1 => omega
      | _ + 2 => rfl
    | _ + 18 => rfl

theorem bb18_2_engine : JZEngine bb18_2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem bb18_2_J0 : bb18_2 9 0 = some ⟨1, Dir.L, some 16⟩ := rfl
private theorem bb18_2_K0 : bb18_2 10 0 = some ⟨1, Dir.R, none⟩ := rfl
private theorem bb18_2_L0 : bb18_2 11 0 = some ⟨1, Dir.L, some 7⟩ := rfl

private theorem bb18_2_rf1 : CanReach bb18_2 (EX 5 []) (EX 14 [1, 1]) := by
  have he := bb18_2_engine
  have h1 : Reaches bb18_2 (EX 5 []) (mkCfgR (some 9) [0, 1, 1, 0, 0, 1] [1, 1, 1]) 16 := by
    show steps bb18_2 16 (EX 5 []) = some (mkCfgR (some 9) [0, 1, 1, 0, 0, 1] [1, 1, 1])
    decide
  have h2 : Reaches bb18_2 (mkCfgR (some 9) [0, 1, 1, 0, 0, 1] [1, 1, 1])
                           (mkCfgR (some 12) [1] [0, 1, 0, 0, 1, 0, 0, 1, 1]) 25 := by
    show steps bb18_2 25 (mkCfgR (some 9) [0, 1, 1, 0, 0, 1] [1, 1, 1]) =
      some (mkCfgR (some 12) [1] [0, 1, 0, 0, 1, 0, 0, 1, 1])
    decide
  apply canReach_trans ⟨16, h1⟩
  apply canReach_trans ⟨25, h2⟩
  apply canReach_trans (jz_M_finish he [1, 0, 0, 1, 0, 0, 1, 1])
  apply canReach_trans (rule_CI_11 he 3 [0, 0, 1, 0, 0, 1, 1])
  apply canReach_trans (rule_CI_10 he 7 [0, 1, 0, 0, 1, 1])
  apply canReach_trans (rule_SW_0 he 0 7 [1, 0, 0, 1, 1])
  apply canReach_trans (rule_CO_10 he 0 10 [0, 1, 1])
  exact rule_CO_0 he 1 10 [1, 1]

private theorem bb18_2_rf2 :
    CanReach bb18_2 (EX 14 [1, 1]) (EX (hoc 0 4 10 + 2 * 4 + 2) [1, 0, 0, 1, 1]) := by
  have he := bb18_2_engine
  have h1 : Reaches bb18_2 (EX 14 [1, 1])
                           (mkCfgR (some 9) (0 :: rep110 4 [0, 1]) [1, 1, 1, 1, 1]) 29 := by
    show steps bb18_2 29 (EX 14 [1, 1]) =
      some (mkCfgR (some 9) (0 :: rep110 4 [0, 1]) [1, 1, 1, 1, 1])
    decide
  have h2 : Reaches bb18_2 (mkCfgR (some 9) (0 :: rep110 4 [0, 1]) [1, 1, 1, 1, 1])
                           (mkCfgR (some 12) (rep110 4 [0, 1]) [0, 1, 0, 0, 1, 0, 0, 1, 1]) 41 := by
    show steps bb18_2 41 (mkCfgR (some 9) (0 :: rep110 4 [0, 1]) [1, 1, 1, 1, 1]) =
      some (mkCfgR (some 12) (rep110 4 [0, 1]) [0, 1, 0, 0, 1, 0, 0, 1, 1])
    decide
  apply canReach_trans ⟨29, h1⟩
  apply canReach_trans ⟨41, h2⟩
  apply canReach_trans ⟨12, jz_M_loop he 4 [0, 1] [1, 0, 0, 1, 0, 0, 1, 1]⟩
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := rep101 4 [1, 0, 0, 1, 0, 0, 1, 1]) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: rep101 4 [1, 0, 0, 1, 0, 0, 1, 1]) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: rep101 4 [1, 0, 0, 1, 0, 0, 1, 1]) he.B1)
  simp only [cons0, rep101]
  apply canReach_trans ⟨3, loop_NOP he 1 1 [] (0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1])⟩
  simp only [rep110]
  apply canReach_step (step_L_cons (a := 1) (L := [1, 0, 1]) (R := 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]) he.N0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := [0, 1]) (R := 0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]) he.A1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := 0 :: 0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]) he.M1)
  simp only [cons0]
  apply canReach_trans (jz_M_finish he (1 :: 0 :: 0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]))
  apply canReach_trans (rule_CI_11 he 3 (0 :: 0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]))
  apply canReach_trans (rule_CI_10 he 7 (0 :: 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]))
  apply canReach_trans (rule_SW_0 he 0 7 (1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1]))
  have hrl : 1 :: rep101 3 [1, 0, 0, 1, 0, 0, 1, 1] =
             rl (rep 4 2 []) [0, 1, 0, 0, 1, 1] := by decide
  rw [hrl]
  apply canReach_trans (CO_chain he 4 0 10 [0, 1, 0, 0, 1, 1])
  rw [Nat.zero_add]
  exact rule_CO_0 he 4 (hoc 0 4 10) [1, 0, 0, 1, 1]

private theorem bb18_2_rf_mod0 (k : Nat) (R' : List Nat) :
    CanReach bb18_2 (EX (3 * (k + 2)) (1 :: R'))
                    (CO 0 10 (rl (rep k 2 []) (1 :: 0 :: 1 :: 1 :: 1 :: R'))) := by
  have he := bb18_2_engine
  unfold EX
  simp only [cons0]
  apply canReach_trans ⟨3 * (k + 2), jz_triJKL he (k + 2) 0 [1] (0 :: 1 :: R')⟩
  change CanReach bb18_2
    (mkCfgR (some 9) (1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (0 :: 1 :: R')) _
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := 1 :: R') bb18_2_J0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 (k + 1) [0, 1]) (R := 1 :: 1 :: R') he.Q1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 0) (L := rep110 (k + 1) [0, 1]) (R := 1 :: 1 :: 1 :: R') he.A1)
  simp only [cons0]
  apply canReach_trans ⟨3 * (k + 1), jz_M_loop he (k + 1) [0, 1] (0 :: 1 :: 1 :: 1 :: R')⟩
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := rep101 (k + 1) (0 :: 1 :: 1 :: 1 :: R')) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: rep101 (k + 1) (0 :: 1 :: 1 :: 1 :: R')) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: rep101 (k + 1) (0 :: 1 :: 1 :: 1 :: R')) he.B1)
  simp only [cons0, rep101]
  apply canReach_trans ⟨3, loop_NOP he 1 1 [] (0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R'))⟩
  simp only [rep110]
  apply canReach_step (step_L_cons (a := 1) (L := [1, 0, 1]) (R := 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')) he.N0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := [0, 1]) (R := 0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')) he.A1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := 0 :: 0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')) he.M1)
  simp only [cons0]
  apply canReach_trans (jz_M_finish he (1 :: 0 :: 0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')))
  apply canReach_trans (rule_CI_11 he 3 (0 :: 0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')))
  apply canReach_trans (rule_CI_10 he 7 (0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')))
  apply canReach_trans (rule_SW_0 he 0 7 (1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R')))
  rw [one_rep101_eq_rl]
  exact canReach_refl bb18_2 _

private theorem bb18_2_rf3 (k : Nat) :
    CanReach bb18_2 (EX (3 * (k + 2)) [1, 0, 0, 1, 1])
                    (EX (iter (ho (k + 1)) 2 (hoc 0 k 10) + 2 * (k + 2) + 2) [1, 1]) := by
  have he := bb18_2_engine
  apply canReach_trans (bb18_2_rf_mod0 k [0, 0, 1, 1])
  apply canReach_trans (CO_chain he k 0 10 [1, 0, 1, 1, 1, 0, 0, 1, 1])
  rw [Nat.zero_add]
  apply canReach_trans (rule_CO_10 he k (hoc 0 k 10) [1, 1, 1, 0, 0, 1, 1])
  apply canReach_trans (CO_iter he 2 (k + 1) (hoc 0 k 10) [0, 0, 1, 1])
  apply canReach_trans (rule_CO_10 he (k + 1) (iter (ho (k + 1)) 2 (hoc 0 k 10)) [0, 1, 1])
  exact rule_CO_0 he (k + 2) (iter (ho (k + 1)) 2 (hoc 0 k 10)) [1, 1]

private theorem bb18_2_rf4 (k : Nat) :
    CanReach bb18_2 (EX (3 * (k + 2)) [1, 1])
                    (EX (iter (ho (k + 1)) 3 (hoc 0 k 10) + 2 * (k + 2) + 2) []) := by
  have he := bb18_2_engine
  apply canReach_trans (bb18_2_rf_mod0 k [1])
  apply canReach_trans (CO_chain he k 0 10 [1, 0, 1, 1, 1, 1])
  rw [Nat.zero_add]
  apply canReach_trans (rule_CO_10 he k (hoc 0 k 10) [1, 1, 1, 1])
  apply canReach_trans (CO_iter he 3 (k + 1) (hoc 0 k 10) [])
  apply canReach_trans (rule_CO_10 he (k + 1) (iter (ho (k + 1)) 3 (hoc 0 k 10)) [])
  exact rule_CO_0 he (k + 2) (iter (ho (k + 1)) 3 (hoc 0 k 10)) []

private theorem bb18_2_rf5_halt (j : Nat) :
    ∃ c, Reaches bb18_2 (EX (3 * j + 1) []) c (3 * j + 2) ∧ c.st = none := by
  have he := bb18_2_engine
  unfold EX
  simp only [cons0]
  have hsplit : rep (3 * j + 1) 1 [] = rep (3 * j) 1 [1] := by
    rw [← rep_add_sym (3 * j) 1 1 []]; rfl
  rw [hsplit]
  have h1 := jz_triJKL he j 0 [1] [1]
  have h2 := reaches_one (step_R_cons (L := rep110 j [0, 1]) (R := []) he.J1)
  have h3 := reaches_one (step_R_zero (L := cons0 0 (rep110 j [0, 1])) (R := []) bb18_2_K0)
  exact ⟨mkCfgR none (cons0 1 (cons0 0 (rep110 j [0, 1]))) [],
         reaches_trans h1 (reaches_trans h2 h3), rfl⟩

theorem bb18_2_halts_gt_f_omega_mul2_2 :
    ValidTM 18 2 bb18_2 ∧
    ∃ s, HaltsIn bb18_2 initConfig s ∧ iter f_omega_mul2 2 (fFin 5 2) < s := by
  refine ⟨bb18_2_valid, ?_⟩
  have he := bb18_2_engine
  obtain ⟨B2, hB2⟩ : ∃ x, x = hoc 0 4 10 + 2 * 4 + 2 := ⟨_, rfl⟩
  have hB2_mod : B2 % 3 = 0 := by
    rw [hB2, Nat.add_mod, Nat.add_mod (hoc 0 4 10), hoc_mod3]
  have hB2_lb : 3 * (fFin 5 2 + 6) ≤ B2 := by
    have hs := seed_bound_hoc3
    have hm := hoc_mono_k (show 3 ≤ 4 by omega) 0 10
    omega
  obtain ⟨k2, hk2⟩ : ∃ k2, B2 = 3 * (k2 + 2) := ⟨B2 / 3 - 2, by omega⟩
  have hk2_eq : k2 = B2 / 3 - 2 := by omega
  obtain ⟨B3, hB3⟩ : ∃ x, x = iter (ho (k2 + 1)) 2 (hoc 0 k2 10) + 2 * (k2 + 2) + 2 := ⟨_, rfl⟩
  have hB3_ge : hoc 0 k2 10 ≤ B3 := by
    have h1 := ho_ge_add4 (k2 + 1) (hoc 0 k2 10)
    have h2 := ho_ge_add4 (k2 + 1) (ho (k2 + 1) (hoc 0 k2 10))
    have e : iter (ho (k2 + 1)) 2 (hoc 0 k2 10) = ho (k2 + 1) (ho (k2 + 1) (hoc 0 k2 10)) := by
      rw [iter_succ, iter_succ, iter_zero]
    omega
  have hB3_mod : B3 % 3 = 0 := by
    have e : iter (ho (k2 + 1)) 2 (hoc 0 k2 10) = ho (k2 + 1) (ho (k2 + 1) (hoc 0 k2 10)) := by
      rw [iter_succ, iter_succ, iter_zero]
    rw [hB3, e, Nat.add_mod, Nat.add_mod (ho _ _), ho_mod3, Nat.add_mod (ho _ _), ho_mod3,
        Nat.add_mod (hoc _ _ _), hoc_mod3]
    omega
  have hB3_lb : 3 * (f_omega_mul2 (fFin 5 2) + 6) ≤ B3 := by
    have hr := hoc_round_step hB2_lb
    rw [← hk2_eq] at hr
    omega
  obtain ⟨k3, hk3⟩ : ∃ k3, B3 = 3 * (k3 + 2) := ⟨B3 / 3 - 2, by omega⟩
  have hk3_eq : k3 = B3 / 3 - 2 := by omega
  obtain ⟨B4, hB4⟩ : ∃ x, x = iter (ho (k3 + 1)) 3 (hoc 0 k3 10) + 2 * (k3 + 2) + 2 := ⟨_, rfl⟩
  have hB4_ge : hoc 0 k3 10 ≤ B4 := by
    have h1 := ho_ge_add4 (k3 + 1) (hoc 0 k3 10)
    have h2 := ho_ge_add4 (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10))
    have h3 := ho_ge_add4 (k3 + 1) (ho (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10)))
    have e : iter (ho (k3 + 1)) 3 (hoc 0 k3 10) =
             ho (k3 + 1) (ho (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10))) := by
      rw [iter_succ, iter_succ, iter_succ, iter_zero]
    omega
  have hB4_mod : B4 % 3 = 1 := by
    have e : iter (ho (k3 + 1)) 3 (hoc 0 k3 10) =
             ho (k3 + 1) (ho (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10))) := by
      rw [iter_succ, iter_succ, iter_succ, iter_zero]
    rw [hB4, e, Nat.add_mod, Nat.add_mod (ho _ _), ho_mod3,
        Nat.add_mod (ho _ _), ho_mod3, Nat.add_mod (ho _ _), ho_mod3,
        Nat.add_mod (hoc _ _ _), hoc_mod3]
    omega
  have hB4_lb : 3 * (f_omega_mul2 (f_omega_mul2 (fFin 5 2)) + 6) ≤ B4 := by
    have hr := hoc_round_step hB3_lb
    rw [← hk3_eq] at hr
    omega
  obtain ⟨j, hj⟩ : ∃ j, B4 = 3 * j + 1 := ⟨B4 / 3, by omega⟩
  have hreach : CanReach bb18_2 initConfig (EX (3 * j + 1) []) := by
    apply canReach_trans ⟨26, jz_boot he⟩
    apply canReach_trans bb18_2_rf1
    apply canReach_trans bb18_2_rf2
    rw [← hB2, hk2]
    apply canReach_trans (bb18_2_rf3 k2)
    rw [← hB3, hk3]
    apply canReach_trans (bb18_2_rf4 k3)
    rw [← hB4, hj]
    exact canReach_refl bb18_2 _
  obtain ⟨t1, ht1⟩ := hreach
  obtain ⟨c, hc, hst⟩ := bb18_2_rf5_halt j
  refine ⟨t1 + (3 * j + 2), ⟨c, reaches_trans ht1 hc, hst⟩, ?_⟩
  have hiter2 : iter f_omega_mul2 2 (fFin 5 2) = f_omega_mul2 (f_omega_mul2 (fFin 5 2)) := by
    rw [iter_succ, iter_succ, iter_zero]
  rw [hiter2]; omega

#print axioms bb18_2_halts_gt_f_omega_mul2_2

end BB
