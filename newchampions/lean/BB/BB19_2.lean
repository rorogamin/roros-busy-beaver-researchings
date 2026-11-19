/-
  BB/BB19_2.lean
  19-state, 2-symbol Busy Beaver champion:
    ValidTM 19 2 bb19_2  ∧  ∃ s, HaltsIn bb19_2 initConfig s ∧ iter f_omega_mul2 5 (fFin 5 2) < s
  Strictly beats the bbchallenge wiki BB(19) champion (> f_{ω×2}^2(f_5(2)))
  and even the wiki BB(20) champion (> f_{ω×2}^3(f_5(2))).

  Uses the shared 15-state Jacobzheng f_{ω×2} engine (BB/Jacobzheng.lean)
  with exit transitions J0=1RZ, K0=1LS, L0=1RK, S0=0LS, S1=0LA.
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.JZMath
import BB.Jacobzheng

namespace BB

def bb19_2 : TM := fun s sym =>
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
  | 9,  0 => some ⟨1, Dir.R, none⟩     -- J0: 1RZ
  | 9,  1 => some ⟨0, Dir.R, some 10⟩  -- J1: 0RK
  | 10, 0 => some ⟨1, Dir.L, some 18⟩  -- K0: 1LS
  | 10, 1 => some ⟨1, Dir.R, some 11⟩  -- K1: 1RL
  | 11, 0 => some ⟨1, Dir.R, some 10⟩  -- L0: 1RK
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
  | 18, 0 => some ⟨0, Dir.L, some 18⟩  -- S0: 0LS
  | 18, 1 => some ⟨0, Dir.L, some 0⟩   -- S1: 0LA
  | _,  _ => none

theorem bb19_2_valid : ValidTM 19 2 bb19_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 =>
      match sym with
      | 0 | 1 => simp [bb19_2]
      | _ + 2 => omega
    | _ + 19 => omega
  · intro s sym h
    match s with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 =>
      match sym with
      | 0 | 1 => omega
      | _ + 2 => rfl
    | _ + 19 => rfl

theorem bb19_2_engine : JZEngine bb19_2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem bb19_2_J0 : bb19_2 9 0 = some ⟨1, Dir.R, none⟩ := rfl
private theorem bb19_2_K0 : bb19_2 10 0 = some ⟨1, Dir.L, some 18⟩ := rfl
private theorem bb19_2_L0 : bb19_2 11 0 = some ⟨1, Dir.R, some 10⟩ := rfl
private theorem bb19_2_S0 : bb19_2 18 0 = some ⟨0, Dir.L, some 18⟩ := rfl
private theorem bb19_2_S1 : bb19_2 18 1 = some ⟨0, Dir.L, some 0⟩ := rfl

private theorem jz_M_to_CO (k a : Nat) (R' : List Nat) :
    CanReach bb19_2 (mkCfgR (some 12) (rep110 (k + 1) [0, 1]) (0 :: a :: R'))
                    (CO 0 10 (rl (rep k 2 []) (1 :: a :: R'))) := by
  have he := bb19_2_engine
  apply canReach_trans ⟨3 * (k + 1), jz_M_loop he (k + 1) [0, 1] (a :: R')⟩
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := rep101 (k + 1) (a :: R')) he.M0)
  simp only [cons0_succ]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: rep101 (k + 1) (a :: R')) he.A0)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: rep101 (k + 1) (a :: R')) he.B1)
  simp only [cons0_succ, rep101]
  apply canReach_trans ⟨3, loop_NOP he 1 1 [] (0 :: 1 :: rep101 k (a :: R'))⟩
  simp only [rep110]
  apply canReach_step (step_L_cons (a := 1) (L := [1, 0, 1]) (R := 1 :: rep101 k (a :: R')) he.N0)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := [0, 1]) (R := 0 :: 1 :: rep101 k (a :: R')) he.A1)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := 0 :: 0 :: 1 :: rep101 k (a :: R')) he.M1)
  simp only [cons0_succ]
  apply canReach_trans (jz_M_finish he (1 :: 0 :: 0 :: 1 :: rep101 k (a :: R')))
  apply canReach_trans (rule_CI_11 he 3 (0 :: 0 :: 1 :: rep101 k (a :: R')))
  apply canReach_trans (rule_CI_10 he 7 (0 :: 1 :: rep101 k (a :: R')))
  apply canReach_trans (rule_SW_0 he 0 7 (1 :: rep101 k (a :: R')))
  rw [one_rep101_eq_rl]
  exact canReach_refl bb19_2 _

private theorem bb19_2_rf1 : CanReach bb19_2 (EX 5 []) (EX 14 [1]) := by
  have he := bb19_2_engine
  have h1 : Reaches bb19_2 (EX 5 []) (mkCfgR (some 12) [1] [0, 1, 0, 0, 1, 0, 0, 1]) 21 := by
    show steps bb19_2 21 (EX 5 []) = some (mkCfgR (some 12) [1] [0, 1, 0, 0, 1, 0, 0, 1])
    decide
  apply canReach_trans ⟨21, h1⟩
  apply canReach_trans (jz_M_finish he [1, 0, 0, 1, 0, 0, 1])
  apply canReach_trans (rule_CI_11 he 3 [0, 0, 1, 0, 0, 1])
  apply canReach_trans (rule_CI_10 he 7 [0, 1, 0, 0, 1])
  apply canReach_trans (rule_SW_0 he 0 7 [1, 0, 0, 1])
  apply canReach_trans (rule_CO_10 he 0 10 [0, 1])
  exact rule_CO_0 he 1 10 [1]

private theorem bb19_2_rf2 :
    CanReach bb19_2 (EX 14 [1]) (EX (iter (ho 3) 2 (hoc 0 3 10) + 2 * 4 + 2) [1]) := by
  have he := bb19_2_engine
  have h1 : Reaches bb19_2 (EX 14 [1])
                           (mkCfgR (some 12) (rep110 4 [0, 1]) [0, 1, 1, 0, 0, 1]) 22 := by
    show steps bb19_2 22 (EX 14 [1]) =
      some (mkCfgR (some 12) (rep110 4 [0, 1]) [0, 1, 1, 0, 0, 1])
    decide
  apply canReach_trans ⟨22, h1⟩
  apply canReach_trans (jz_M_to_CO 3 1 [1, 0, 0, 1])
  apply canReach_trans (CO_chain he 3 0 10 [1, 1, 1, 0, 0, 1])
  rw [Nat.zero_add]
  apply canReach_trans (CO_iter he 2 3 (hoc 0 3 10) [0, 0, 1])
  apply canReach_trans (rule_CO_10 he 3 (iter (ho 3) 2 (hoc 0 3 10)) [0, 1])
  exact rule_CO_0 he 4 (iter (ho 3) 2 (hoc 0 3 10)) [1]

private theorem bb19_2_rf_mod1 (k hd : Nat) (tl : List Nat) :
    CanReach bb19_2 (EX (3 * (k + 2) + 1) (hd :: tl))
                    (EX (hoc 0 k 10 + 2 * (k + 1) + 2) (0 :: 1 :: hd :: tl)) := by
  have he := bb19_2_engine
  unfold EX; simp only [cons0_cons]
  have hsplit : rep (3 * (k + 2) + 1) 1 (0 :: hd :: tl) =
                rep (3 * (k + 2)) 1 (1 :: 0 :: hd :: tl) := by
    rw [← rep_add_sym (3 * (k + 2)) 1 1 (0 :: hd :: tl)]; rfl
  rw [hsplit]
  apply canReach_trans ⟨3 * (k + 2), jz_triJKL he (k + 2) 0 [1] (1 :: 0 :: hd :: tl)⟩
  apply canReach_step (step_R_cons (L := rep110 (k + 2) [0, 1]) (R := 0 :: hd :: tl) he.J1)
  rw [cons0_ne_nil 0 (by simp [rep110])]
  apply canReach_step (step_L_cons (a := 0) (L := rep110 (k + 2) [0, 1]) (R := hd :: tl) bb19_2_K0)
  simp only [cons0_succ]
  change CanReach bb19_2
    (mkCfgR (some 18) (1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (0 :: 1 :: hd :: tl)) _
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := 1 :: hd :: tl) bb19_2_S0)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 (k + 1) [0, 1]) (R := 0 :: 1 :: hd :: tl) bb19_2_S1)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 0) (L := rep110 (k + 1) [0, 1]) (R := 0 :: 0 :: 1 :: hd :: tl) he.A1)
  simp only [cons0_cons]
  apply canReach_trans (jz_M_to_CO k 0 (0 :: 0 :: 1 :: hd :: tl))
  apply canReach_trans (CO_chain he k 0 10 (1 :: 0 :: 0 :: 0 :: 1 :: hd :: tl))
  rw [Nat.zero_add]
  apply canReach_trans (rule_CO_10 he k (hoc 0 k 10) (0 :: 0 :: 1 :: hd :: tl))
  exact rule_CO_0 he (k + 1) (hoc 0 k 10) (0 :: 1 :: hd :: tl)

private theorem bb19_2_rf_mod2_0 (k hd : Nat) (tl : List Nat) :
    CanReach bb19_2 (EX (3 * (k + 1) + 2) (0 :: hd :: tl))
                    (EX (hoc 0 k 10 + 2 * (k + 1) + 2) (1 :: hd :: tl)) := by
  have he := bb19_2_engine
  unfold EX; simp only [cons0_cons]
  have hsplit : rep (3 * (k + 1) + 2) 1 (0 :: 0 :: hd :: tl) =
                rep (3 * (k + 1)) 1 (1 :: 1 :: 0 :: 0 :: hd :: tl) := by
    rw [← rep_add_sym (3 * (k + 1)) 2 1 (0 :: 0 :: hd :: tl)]; rfl
  rw [hsplit]
  apply canReach_trans ⟨3 * (k + 1), jz_triJKL he (k + 1) 0 [1] (1 :: 1 :: 0 :: 0 :: hd :: tl)⟩
  apply canReach_step (step_R_cons (L := rep110 (k + 1) [0, 1]) (R := 1 :: 0 :: 0 :: hd :: tl) he.J1)
  rw [cons0_ne_nil 0 (by simp [rep110])]
  apply canReach_step (step_R_cons (L := 0 :: rep110 (k + 1) [0, 1]) (R := 0 :: 0 :: hd :: tl) he.K1)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := 0 :: hd :: tl) bb19_2_L0)
  simp only [cons0_succ]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := hd :: tl) bb19_2_K0)
  simp only [cons0_succ]
  apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 (k + 1) [0, 1]) (R := 1 :: hd :: tl) bb19_2_S1)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 0) (L := rep110 (k + 1) [0, 1]) (R := 0 :: 1 :: hd :: tl) he.A1)
  simp only [cons0_cons]
  apply canReach_trans (jz_M_to_CO k 0 (0 :: 1 :: hd :: tl))
  apply canReach_trans (CO_chain he k 0 10 (1 :: 0 :: 0 :: 1 :: hd :: tl))
  rw [Nat.zero_add]
  apply canReach_trans (rule_CO_10 he k (hoc 0 k 10) (0 :: 1 :: hd :: tl))
  exact rule_CO_0 he (k + 1) (hoc 0 k 10) (1 :: hd :: tl)

private theorem bb19_2_rf5 (k : Nat) :
    CanReach bb19_2 (EX (3 * (k + 1) + 2) [1, 1, 1])
                    (EX (iter (ho k) 2 (hoc 0 k 10) + 2 * (k + 1) + 2) [0, 1]) := by
  have he := bb19_2_engine
  unfold EX; simp only [cons0_cons]
  have hsplit : rep (3 * (k + 1) + 2) 1 [0, 1, 1, 1] =
                rep (3 * (k + 1)) 1 [1, 1, 0, 1, 1, 1] := by
    rw [← rep_add_sym (3 * (k + 1)) 2 1 [0, 1, 1, 1]]; rfl
  rw [hsplit]
  apply canReach_trans ⟨3 * (k + 1), jz_triJKL he (k + 1) 0 [1] [1, 1, 0, 1, 1, 1]⟩
  apply canReach_step (step_R_cons (L := rep110 (k + 1) [0, 1]) (R := [1, 0, 1, 1, 1]) he.J1)
  rw [cons0_ne_nil 0 (by simp [rep110])]
  apply canReach_step (step_R_cons (L := 0 :: rep110 (k + 1) [0, 1]) (R := [0, 1, 1, 1]) he.K1)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [1, 1, 1]) bb19_2_L0)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [1, 1]) he.K1)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := 1 :: 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [1]) he.L1)
  simp only [cons0_succ]
  apply canReach_step (step_R_cons (L := 1 :: 1 :: 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := []) he.J1)
  simp only [cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 0) (L := 1 :: 1 :: 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := []) bb19_2_K0)
  simp only [cons0_succ]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [1]) bb19_2_S0)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [0, 1]) bb19_2_S1)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 (k + 1) [0, 1]) (R := [0, 0, 1]) he.A1)
  simp only [cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 (k + 1) [0, 1]) (R := [0, 0, 0, 1]) he.M1)
  simp only [cons0_succ]
  apply canReach_step (step_L_cons (a := 0) (L := rep110 (k + 1) [0, 1]) (R := [1, 0, 0, 0, 1]) he.M1)
  simp only [cons0_succ]
  apply canReach_trans (jz_M_to_CO k 1 [1, 0, 0, 0, 1])
  apply canReach_trans (CO_chain he k 0 10 [1, 1, 1, 0, 0, 0, 1])
  rw [Nat.zero_add]
  apply canReach_trans (CO_iter he 2 k (hoc 0 k 10) [0, 0, 0, 1])
  apply canReach_trans (rule_CO_10 he k (iter (ho k) 2 (hoc 0 k 10)) [0, 0, 1])
  exact rule_CO_0 he (k + 1) (iter (ho k) 2 (hoc 0 k 10)) [0, 1]

private theorem bb19_2_rf8_halt (j : Nat) :
    ∃ c, Reaches bb19_2 (EX (3 * j + 2) [1, 1, 0, 1]) c (3 * j + 6) ∧ c.st = none := by
  have he := bb19_2_engine
  unfold EX; simp only [cons0_cons]
  have hsplit : rep (3 * j + 2) 1 [0, 1, 1, 0, 1] =
                rep (3 * j) 1 [1, 1, 0, 1, 1, 0, 1] := by
    rw [← rep_add_sym (3 * j) 2 1 [0, 1, 1, 0, 1]]; rfl
  rw [hsplit]
  have h1 := jz_triJKL he j 0 [1] [1, 1, 0, 1, 1, 0, 1]
  have h2 := reaches_one (step_R_cons (L := rep110 j [0, 1]) (R := [1, 0, 1, 1, 0, 1]) he.J1)
  rw [cons0_ne_nil 0 (by cases j <;> simp [rep110])] at h2
  have h3 := reaches_one (step_R_cons (L := 0 :: rep110 j [0, 1]) (R := [0, 1, 1, 0, 1]) he.K1)
  have h4 := reaches_one (step_R_cons (L := 1 :: 0 :: rep110 j [0, 1]) (R := [1, 1, 0, 1]) bb19_2_L0)
  have h5 := reaches_one (step_R_cons (L := 1 :: 1 :: 0 :: rep110 j [0, 1]) (R := [1, 0, 1]) he.K1)
  have h6 := reaches_one (step_R_cons (L := 1 :: 1 :: 1 :: 0 :: rep110 j [0, 1]) (R := [0, 1]) he.L1)
  have h7 := reaches_one (step_R_cons (L := 1 :: 1 :: 1 :: 1 :: 0 :: rep110 j [0, 1]) (R := [1]) bb19_2_J0)
  simp only [cons0_succ] at h3 h4 h5 h6 h7
  exact ⟨_, reaches_trans h1 (reaches_trans h2 (reaches_trans h3
            (reaches_trans h4 (reaches_trans h5 (reaches_trans h6 h7))))), rfl⟩

theorem bb19_2_halts_gt_f_omega_mul2_5 :
    ValidTM 19 2 bb19_2 ∧
    ∃ s, HaltsIn bb19_2 initConfig s ∧ iter f_omega_mul2 5 (fFin 5 2) < s := by
  refine ⟨bb19_2_valid, ?_⟩
  have he := bb19_2_engine
  have hiter_mod : ∀ m k x, iter (ho m) k x % 3 = (x + k) % 3 := by
    intro m k; induction k with
    | zero => intro x; simp [iter]
    | succ p ih => intro x; rw [iter_succ, ho_mod3, Nat.add_mod, ih]; omega
  obtain ⟨x0, hx0⟩ : ∃ x, x = fFin 5 2 := ⟨_, rfl⟩
  have hx0_seed : 3 * (x0 + 6) + 10 ≤ hoc 0 3 10 := by rw [hx0]; exact seed_bound_hoc3
  have hit : ∀ k, iter f_omega_mul2 (k + 1) x0 = f_omega_mul2 (iter f_omega_mul2 k x0) :=
    fun k => iter_succ f_omega_mul2 k x0
  -- Round 2: B2 (% 3 = 1)
  obtain ⟨B2, hB2⟩ : ∃ x, x = iter (ho 3) 2 (hoc 0 3 10) + 2 * 4 + 2 := ⟨_, rfl⟩
  have hB2_ge : hoc 0 3 10 ≤ B2 := by
    have h1 := ho_ge_add4 3 (hoc 0 3 10)
    have h2 := ho_ge_add4 3 (ho 3 (hoc 0 3 10))
    have e : iter (ho 3) 2 (hoc 0 3 10) = ho 3 (ho 3 (hoc 0 3 10)) := by
      rw [iter_succ, iter_succ, iter_zero]
    omega
  have hB2_mod : B2 % 3 = 1 := by
    rw [hB2, Nat.add_mod, Nat.add_mod (iter _ _ _), hiter_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]
  have hB2_lb : 3 * (x0 + 6) ≤ B2 := by omega
  obtain ⟨k2, hk2⟩ : ∃ k2, B2 = 3 * (k2 + 2) + 1 := ⟨B2 / 3 - 2, by omega⟩
  have hk2_eq : k2 = B2 / 3 - 2 := by omega
  -- Round 3 (RF_mod1): B3 (% 3 = 2)
  obtain ⟨B3, hB3⟩ : ∃ x, x = hoc 0 k2 10 + 2 * (k2 + 1) + 2 := ⟨_, rfl⟩
  have hB3_mod : B3 % 3 = 2 := by
    rw [hB3, Nat.add_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]; omega
  have hB3_lb : 3 * (iter f_omega_mul2 1 x0 + 6) ≤ B3 := by
    have hr := hoc_round_step hB2_lb; rw [← hk2_eq] at hr
    rw [show iter f_omega_mul2 1 x0 = f_omega_mul2 x0 from rfl]; omega
  obtain ⟨k3, hk3⟩ : ∃ k3, B3 = 3 * (k3 + 1) + 2 := ⟨B3 / 3 - 1, by omega⟩
  have hk3_ge : B3 / 3 - 2 ≤ k3 := by omega
  -- Round 4 (RF_mod2_0): B4 (% 3 = 2)
  obtain ⟨B4, hB4⟩ : ∃ x, x = hoc 0 k3 10 + 2 * (k3 + 1) + 2 := ⟨_, rfl⟩
  have hB4_mod : B4 % 3 = 2 := by
    rw [hB4, Nat.add_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]; omega
  have hB4_lb : 3 * (iter f_omega_mul2 2 x0 + 6) ≤ B4 := by
    have hr := hoc_round_step hB3_lb; have hm := hoc_mono_k hk3_ge 0 10
    rw [hit 1]; omega
  obtain ⟨k4, hk4⟩ : ∃ k4, B4 = 3 * (k4 + 1) + 2 := ⟨B4 / 3 - 1, by omega⟩
  have hk4_ge : B4 / 3 - 2 ≤ k4 := by omega
  -- Round 5 (RF5): B5 (% 3 = 1)
  obtain ⟨B5, hB5⟩ : ∃ x, x = iter (ho k4) 2 (hoc 0 k4 10) + 2 * (k4 + 1) + 2 := ⟨_, rfl⟩
  have hB5_ge : hoc 0 k4 10 ≤ B5 := by
    have h1 := ho_ge_add4 k4 (hoc 0 k4 10)
    have h2 := ho_ge_add4 k4 (ho k4 (hoc 0 k4 10))
    have e : iter (ho k4) 2 (hoc 0 k4 10) = ho k4 (ho k4 (hoc 0 k4 10)) := by
      rw [iter_succ, iter_succ, iter_zero]
    omega
  have hB5_mod : B5 % 3 = 1 := by
    rw [hB5, Nat.add_mod, Nat.add_mod (iter _ _ _), hiter_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]
    omega
  have hB5_lb : 3 * (iter f_omega_mul2 3 x0 + 6) ≤ B5 := by
    have hr := hoc_round_step hB4_lb; have hm := hoc_mono_k hk4_ge 0 10
    rw [hit 2]; omega
  obtain ⟨k5, hk5⟩ : ∃ k5, B5 = 3 * (k5 + 2) + 1 := ⟨B5 / 3 - 2, by omega⟩
  have hk5_eq : k5 = B5 / 3 - 2 := by omega
  -- Round 6 (RF_mod1): B6 (% 3 = 2)
  obtain ⟨B6, hB6⟩ : ∃ x, x = hoc 0 k5 10 + 2 * (k5 + 1) + 2 := ⟨_, rfl⟩
  have hB6_mod : B6 % 3 = 2 := by
    rw [hB6, Nat.add_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]; omega
  have hB6_lb : 3 * (iter f_omega_mul2 4 x0 + 6) ≤ B6 := by
    have hr := hoc_round_step hB5_lb; rw [← hk5_eq] at hr
    rw [hit 3]; omega
  obtain ⟨k6, hk6⟩ : ∃ k6, B6 = 3 * (k6 + 1) + 2 := ⟨B6 / 3 - 1, by omega⟩
  have hk6_ge : B6 / 3 - 2 ≤ k6 := by omega
  -- Round 7 (RF_mod2_0): B7 (% 3 = 2)
  obtain ⟨B7, hB7⟩ : ∃ x, x = hoc 0 k6 10 + 2 * (k6 + 1) + 2 := ⟨_, rfl⟩
  have hB7_mod : B7 % 3 = 2 := by
    rw [hB7, Nat.add_mod, Nat.add_mod (hoc _ _ _), hoc_mod3]; omega
  have hB7_lb : 3 * (iter f_omega_mul2 5 x0 + 6) ≤ B7 := by
    have hr := hoc_round_step hB6_lb; have hm := hoc_mono_k hk6_ge 0 10
    rw [hit 4]; omega
  obtain ⟨j, hj⟩ : ∃ j, B7 = 3 * j + 2 := ⟨B7 / 3, by omega⟩
  have hreach : CanReach bb19_2 initConfig (EX (3 * j + 2) [1, 1, 0, 1]) := by
    apply canReach_trans ⟨26, jz_boot he⟩
    apply canReach_trans bb19_2_rf1
    apply canReach_trans bb19_2_rf2
    rw [← hB2, hk2]
    apply canReach_trans (bb19_2_rf_mod1 k2 1 [])
    rw [← hB3, hk3]
    apply canReach_trans (bb19_2_rf_mod2_0 k3 1 [1])
    rw [← hB4, hk4]
    apply canReach_trans (bb19_2_rf5 k4)
    rw [← hB5, hk5]
    apply canReach_trans (bb19_2_rf_mod1 k5 0 [1])
    rw [← hB6, hk6]
    apply canReach_trans (bb19_2_rf_mod2_0 k6 1 [0, 1])
    rw [← hB7, hj]
    exact canReach_refl bb19_2 _
  obtain ⟨t1, ht1⟩ := hreach
  obtain ⟨c, hc, hst⟩ := bb19_2_rf8_halt j
  exact ⟨t1 + (3 * j + 6), ⟨c, reaches_trans ht1 hc, hst⟩, by rw [← hx0]; omega⟩

#print axioms bb19_2_halts_gt_f_omega_mul2_5

end BB
