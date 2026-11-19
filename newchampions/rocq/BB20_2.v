(*
  rocq/BB20_2.v
  20-state, 2-symbol Busy Beaver champion:
    ValidTM 20 2 bb20_2  /\  exists s, HaltsIn bb20_2 initConfig s /\ iter f_omega_mul2 8 (fFin 5 2) < s
  Strictly beats the bbchallenge wiki BB(20) champion (> f_{ω×2}^3(f_5(2))).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz JZMath Jacobzheng.
Import ListNotations.

Definition bb20_2 : TM := fun s sym =>
  match s, sym with
  | 0,  0 => Some (mkAction 1 DL (Some 1))   (* A0: 1LB *)
  | 0,  1 => Some (mkAction 0 DL (Some 12))  (* A1: 0LM *)
  | 1,  0 => Some (mkAction 1 DR (Some 2))   (* B0: 1RC *)
  | 1,  1 => Some (mkAction 1 DR (Some 13))  (* B1: 1RN *)
  | 2,  0 => Some (mkAction 1 DR (Some 3))   (* C0: 1RD *)
  | 2,  1 => Some (mkAction 1 DR (Some 2))   (* C1: 1RC *)
  | 3,  0 => Some (mkAction 0 DL (Some 4))   (* D0: 0LE *)
  | 3,  1 => Some (mkAction 1 DR (Some 16))  (* D1: 1RQ *)
  | 4,  0 => Some (mkAction 1 DL (Some 5))   (* E0: 1LF *)
  | 4,  1 => Some (mkAction 1 DL (Some 4))   (* E1: 1LE *)
  | 5,  0 => Some (mkAction 0 DL (Some 6))   (* F0: 0LG *)
  | 5,  1 => Some (mkAction 1 DL (Some 4))   (* F1: 1LE *)
  | 6,  0 => Some (mkAction 1 DR (Some 7))   (* G0: 1RH *)
  | 6,  1 => Some (mkAction 1 DR (Some 8))   (* G1: 1RI *)
  | 7,  0 => Some (mkAction 0 DR (Some 7))   (* H0: 0RH *)
  | 7,  1 => Some (mkAction 0 DR (Some 2))   (* H1: 0RC *)
  | 8,  0 => Some (mkAction 0 DR (Some 9))   (* I0: 0RJ *)
  | 8,  1 => Some (mkAction 1 DR (Some 7))   (* I1: 1RH *)
  | 9,  0 => Some (mkAction 0 DR (Some 19))  (* J0: 0RT *)
  | 9,  1 => Some (mkAction 0 DR (Some 10))  (* J1: 0RK *)
  | 10, 0 => Some (mkAction 1 DL (Some 18))  (* K0: 1LS *)
  | 10, 1 => Some (mkAction 1 DR (Some 11))  (* K1: 1RL *)
  | 11, 0 => Some (mkAction 1 DR (Some 10))  (* L0: 1RK *)
  | 11, 1 => Some (mkAction 1 DR (Some 9))   (* L1: 1RJ *)
  | 12, 0 => Some (mkAction 1 DL (Some 0))   (* M0: 1LA *)
  | 12, 1 => Some (mkAction 1 DL (Some 12))  (* M1: 1LM *)
  | 13, 0 => Some (mkAction 0 DL (Some 0))   (* N0: 0LA *)
  | 13, 1 => Some (mkAction 0 DR (Some 14))  (* N1: 0RO *)
  | 14, 0 => Some (mkAction 0 DL (Some 2))   (* O0: 0LC *)
  | 14, 1 => Some (mkAction 1 DR (Some 15))  (* O1: 1RP *)
  | 15, 0 => Some (mkAction 0 DL (Some 0))   (* P0: 0LA *)
  | 15, 1 => Some (mkAction 1 DR (Some 13))  (* P1: 1RN *)
  | 16, 0 => Some (mkAction 0 DL (Some 17))  (* Q0: 0LR *)
  | 16, 1 => Some (mkAction 1 DL (Some 0))   (* Q1: 1LA *)
  | 17, 0 => Some (mkAction 0 DR (Some 8))   (* R0: 0RI *)
  | 17, 1 => Some (mkAction 1 DL (Some 17))  (* R1: 1LR *)
  | 18, 0 => Some (mkAction 0 DL (Some 18))  (* S0: 0LS *)
  | 18, 1 => Some (mkAction 0 DL (Some 0))   (* S1: 0LA *)
  | 19, 0 => Some (mkAction 1 DR None)       (* T0: 1RZ *)
  | 19, 1 => Some (mkAction 0 DR (Some 10))  (* T1: 0RK *)
  | _,  _ => None
  end.

Lemma bb20_2_valid : ValidTM 20 2 bb20_2.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 20 (destruct s as [| s]; [
      do 2 (destruct sym as [| sym]; [simpl; lia |]); lia
    |]); lia.
  - do 20 (destruct s as [| s]; [
      do 2 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb20_2_engine : JZEngine bb20_2.
Proof. constructor; reflexivity. Qed.

Local Lemma bb20_2_J0 : bb20_2 9 0 = Some (mkAction 0 DR (Some 19)). Proof. reflexivity. Qed.
Local Lemma bb20_2_K0 : bb20_2 10 0 = Some (mkAction 1 DL (Some 18)). Proof. reflexivity. Qed.
Local Lemma bb20_2_L0 : bb20_2 11 0 = Some (mkAction 1 DR (Some 10)). Proof. reflexivity. Qed.
Local Lemma bb20_2_S0 : bb20_2 18 0 = Some (mkAction 0 DL (Some 18)). Proof. reflexivity. Qed.
Local Lemma bb20_2_S1 : bb20_2 18 1 = Some (mkAction 0 DL (Some 0)). Proof. reflexivity. Qed.
Local Lemma bb20_2_T0 : bb20_2 19 0 = Some (mkAction 1 DR None). Proof. reflexivity. Qed.
Local Lemma bb20_2_T1 : bb20_2 19 1 = Some (mkAction 0 DR (Some 10)). Proof. reflexivity. Qed.

Local Lemma jz_M_to_CO : forall k a R',
  CanReach bb20_2 (mkCfgR (Some 12) (rep110 (k + 1) [0; 1]) (0 :: a :: R'))
                  (CO 0 10 (rl (rep k 2 []) (1 :: a :: R'))).
Proof.
  intros k a R'. pose proof bb20_2_engine as He.
  eapply canReach_trans; [exists (3 * (k + 1)); exact (jz_M_loop _ He (k + 1) [0; 1] (a :: R')) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B1 _ He) | simp_cons0].
  replace (k + 1) with (S k) by lia. simpl rep101.
  eapply canReach_trans; [exists 3; exact (loop_NOP _ He 1 1 [] (0 :: 1 :: rep101 k (a :: R'))) |].
  simpl rep110.
  eapply canReach_step; [eapply step_L_cons; apply (jz_N0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [apply (jz_M_finish _ He) |].
  eapply canReach_trans; [apply (rule_CI_11 _ He) |].
  eapply canReach_trans; [apply (rule_CI_10 _ He 7 (0 :: 1 :: rep101 k (a :: R'))) |].
  eapply canReach_trans; [apply (rule_SW_0 _ He 0 7 (1 :: rep101 k (a :: R'))) |].
  rewrite one_rep101_eq_rl.
  apply canReach_refl.
Qed.

Local Lemma bb20_2_rf1 : CanReach bb20_2 (EX 5 []) (EX 14 [1]).
Proof.
  pose proof bb20_2_engine as He.
  assert (H1 : Reaches bb20_2 (EX 5 []) (mkCfgR (Some 12) [1] [0; 1; 0; 0; 1; 0; 0; 1]) 21)
    by reflexivity.
  eapply canReach_trans; [exists 21; exact H1 |].
  eapply canReach_trans; [apply (jz_M_finish _ He) |].
  eapply canReach_trans; [apply (rule_CI_11 _ He) |].
  eapply canReach_trans; [apply (rule_CI_10 _ He 7 [0; 1; 0; 0; 1]) |].
  eapply canReach_trans; [apply (rule_SW_0 _ He 0 7 [1; 0; 0; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He 0 10 [0; 1]) |].
  apply (rule_CO_0 _ He 1 10 [1]).
Qed.

Local Lemma bb20_2_rf2 :
  CanReach bb20_2 (EX 14 [1]) (EX (iter (ho 3) 2 (hoc 0 3 10) + 2 * 4 + 2) [1]).
Proof.
  pose proof bb20_2_engine as He.
  assert (H1 : Reaches bb20_2 (EX 14 [1])
                              (mkCfgR (Some 12) (rep110 4 [0; 1]) [0; 1; 1; 0; 0; 1]) 22)
    by reflexivity.
  eapply canReach_trans; [exists 22; exact H1 |].
  eapply canReach_trans; [exact (jz_M_to_CO 3 1 [1; 0; 0; 1]) |].
  eapply canReach_trans; [apply (CO_chain _ He 3 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (CO_iter _ He 2 3 (hoc 0 3 10) [0; 0; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He 3 _ [0; 1]) |].
  apply (rule_CO_0 _ He 4 _ [1]).
Qed.

Local Lemma bb20_2_rf_mod1 : forall k hd tl,
  CanReach bb20_2 (EX (3 * (k + 2) + 1) (hd :: tl))
                  (EX (hoc 0 k 10 + 2 * (k + 1) + 2) (0 :: 1 :: hd :: tl)).
Proof.
  intros k hd tl. pose proof bb20_2_engine as He. unfold EX. simp_cons0.
  assert (Hs : rep (3 * (k + 2) + 1) 1 (0 :: hd :: tl) =
               rep (3 * (k + 2)) 1 (1 :: 0 :: hd :: tl)).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hs.
  eapply canReach_trans; [exists (3 * (k + 2)); exact (jz_triJKL _ He (k + 2) 0 [1] (1 :: 0 :: hd :: tl)) |].
  eapply canReach_step; [eapply step_R_cons; apply (jz_J1 _ He) |].
  rewrite cons0_ne_nil by (replace (k + 2) with (S (k + 1)) by lia; simpl; discriminate).
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_K0 | simp_cons0].
  replace (k + 2) with (S (k + 1)) by lia. simpl rep110.
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S1 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exact (jz_M_to_CO k 0 (0 :: 0 :: 1 :: hd :: tl)) |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (rule_CO_10 _ He k (hoc 0 k 10) (0 :: 0 :: 1 :: hd :: tl)) |].
  replace (S k) with (k + 1) by lia.
  apply (rule_CO_0 _ He (k + 1) (hoc 0 k 10) (0 :: 1 :: hd :: tl)).
Qed.

Local Lemma bb20_2_rf_mod2_0 : forall k hd tl,
  CanReach bb20_2 (EX (3 * (k + 1) + 2) (0 :: hd :: tl))
                  (EX (hoc 0 k 10 + 2 * (k + 1) + 2) (1 :: hd :: tl)).
Proof.
  intros k hd tl. pose proof bb20_2_engine as He. unfold EX. simp_cons0.
  assert (Hs : rep (3 * (k + 1) + 2) 1 (0 :: 0 :: hd :: tl) =
               rep (3 * (k + 1)) 1 (1 :: 1 :: 0 :: 0 :: hd :: tl)).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hs.
  eapply canReach_trans; [exists (3 * (k + 1)); exact (jz_triJKL _ He (k + 1) 0 [1] (1 :: 1 :: 0 :: 0 :: hd :: tl)) |].
  eapply canReach_step; [eapply step_R_cons; apply (jz_J1 _ He) |].
  rewrite cons0_ne_nil by (replace (k + 1) with (S k) by lia; simpl; discriminate).
  eapply canReach_step; [eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply bb20_2_L0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_K0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S1 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exact (jz_M_to_CO k 0 (0 :: 1 :: hd :: tl)) |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (rule_CO_10 _ He k (hoc 0 k 10) (0 :: 1 :: hd :: tl)) |].
  replace (S k) with (k + 1) by lia.
  apply (rule_CO_0 _ He (k + 1) (hoc 0 k 10) (1 :: hd :: tl)).
Qed.

Local Lemma bb20_2_rf5 : forall k,
  CanReach bb20_2 (EX (3 * (k + 1) + 2) [1; 1; 1])
                  (EX (iter (ho k) 2 (hoc 0 k 10) + 2 * (k + 1) + 2) [0; 1]).
Proof.
  intro k. pose proof bb20_2_engine as He. unfold EX. simp_cons0.
  assert (Hs : rep (3 * (k + 1) + 2) 1 [0; 1; 1; 1] =
               rep (3 * (k + 1)) 1 [1; 1; 0; 1; 1; 1]).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hs.
  eapply canReach_trans; [exists (3 * (k + 1)); exact (jz_triJKL _ He (k + 1) 0 [1] [1; 1; 0; 1; 1; 1]) |].
  eapply canReach_step; [eapply step_R_cons; apply (jz_J1 _ He) |].
  rewrite cons0_ne_nil by (replace (k + 1) with (S k) by lia; simpl; discriminate).
  eapply canReach_step; [eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply bb20_2_L0 | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_L1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_J1 _ He) | simp_cons0].
  eapply canReach_step; [apply (step_L_zero_cons _ _ _ _ _ _ [] bb20_2_K0) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S1 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [exact (jz_M_to_CO k 1 [1; 0; 0; 0; 1]) |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (CO_iter _ He 2 k (hoc 0 k 10) [0; 0; 0; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He k _ [0; 0; 1]) |].
  replace (S k) with (k + 1) by lia.
  apply (rule_CO_0 _ He (k + 1) _ [0; 1]).
Qed.

Local Lemma bb20_2_rf8 : forall k,
  CanReach bb20_2 (EX (3 * (k + 1) + 2) [1; 1; 0; 1])
                  (EX (iter (ho k) 2 (hoc 0 k 10) + 2 * (k + 1) + 2) [0; 0; 1]).
Proof.
  intro k. pose proof bb20_2_engine as He. unfold EX. simp_cons0.
  assert (Hs : rep (3 * (k + 1) + 2) 1 [0; 1; 1; 0; 1] =
               rep (3 * (k + 1)) 1 [1; 1; 0; 1; 1; 0; 1]).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hs.
  eapply canReach_trans; [exists (3 * (k + 1)); exact (jz_triJKL _ He (k + 1) 0 [1] [1; 1; 0; 1; 1; 0; 1]) |].
  eapply canReach_step; [eapply step_R_cons; apply (jz_J1 _ He) |].
  rewrite cons0_ne_nil by (replace (k + 1) with (S k) by lia; simpl; discriminate).
  eapply canReach_step; [eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply bb20_2_L0 | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_K1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_L1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply bb20_2_J0 | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply bb20_2_T1 | simp_cons0].
  eapply canReach_step; [apply (step_L_zero_cons _ _ _ _ _ _ [] bb20_2_K0) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply bb20_2_S1 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [exact (jz_M_to_CO k 1 [1; 0; 0; 0; 0; 1]) |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (CO_iter _ He 2 k (hoc 0 k 10) [0; 0; 0; 0; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He k _ [0; 0; 0; 1]) |].
  replace (S k) with (k + 1) by lia.
  apply (rule_CO_0 _ He (k + 1) _ [0; 0; 1]).
Qed.

Local Lemma bb20_2_rf11_halt : forall j,
  exists c, Reaches bb20_2 (EX (3 * j + 2) [1; 1; 0; 0; 1]) c (3 * j + 7) /\ cfg_st c = None.
Proof.
  intro j. pose proof bb20_2_engine as He. unfold EX. simp_cons0.
  assert (Hs : rep (3 * j + 2) 1 [0; 1; 1; 0; 0; 1] =
               rep (3 * j) 1 [1; 1; 0; 1; 1; 0; 0; 1]).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hs.
  pose proof (jz_triJKL _ He j 0 [1] [1; 1; 0; 1; 1; 0; 0; 1]) as H1.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (rep110 j [0; 1]) [1; 0; 1; 1; 0; 0; 1] (jz_J1 _ He))) as H2.
  rewrite cons0_ne_nil in H2 by (destruct j; discriminate).
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (0 :: rep110 j [0; 1]) [0; 1; 1; 0; 0; 1] (jz_K1 _ He))) as H3.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (1 :: 0 :: rep110 j [0; 1]) [1; 1; 0; 0; 1] bb20_2_L0)) as H4.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (1 :: 1 :: 0 :: rep110 j [0; 1]) [1; 0; 0; 1] (jz_K1 _ He))) as H5.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (1 :: 1 :: 1 :: 0 :: rep110 j [0; 1]) [0; 0; 1] (jz_L1 _ He))) as H6.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (1 :: 1 :: 1 :: 1 :: 0 :: rep110 j [0; 1]) [0; 1] bb20_2_J0)) as H7.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (0 :: 1 :: 1 :: 1 :: 1 :: 0 :: rep110 j [0; 1]) [1] bb20_2_T0)) as H8.
  rewrite ?jz_cons0_succ, ?jz_cons0_cons in H3, H4, H5, H6, H7, H8.
  eexists. split.
  - replace (3 * j + 7) with (3 * j + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) by lia.
    eapply reaches_trans; [exact H1 |].
    eapply reaches_trans; [exact H2 |].
    eapply reaches_trans; [exact H3 |].
    eapply reaches_trans; [exact H4 |].
    eapply reaches_trans; [exact H5 |].
    eapply reaches_trans; [exact H6 |].
    eapply reaches_trans; [exact H7 | exact H8].
  - reflexivity.
Qed.

Theorem bb20_2_halts_gt_f_omega_mul2_8 :
  ValidTM 20 2 bb20_2 /\
  exists s, HaltsIn bb20_2 initConfig s /\ iter f_omega_mul2 8 (fFin 5 2) < s.
Proof.
  split; [exact bb20_2_valid |].
  pose proof bb20_2_engine as He.
  assert (Hiter_mod : forall m k x, iter (ho m) k x mod 3 = (x + k) mod 3).
  { intros m k. induction k as [| p IH]; intro x; cbn [iter].
    - replace (x + 0) with x by lia. reflexivity.
    - rewrite ho_mod3, <- Nat.Div0.add_mod_idemp_l, IH, Nat.Div0.add_mod_idemp_l. f_equal. lia. }
  assert (Hmod3 : forall a b c d, a mod 3 = d mod 3 -> (a + b + c) mod 3 = (d + b + c) mod 3).
  { intros a b c d H.
    rewrite Nat.Div0.add_mod, (Nat.Div0.add_mod a b 3), H,
            <- (Nat.Div0.add_mod d b 3), <- Nat.Div0.add_mod. reflexivity. }
  remember (fFin 5 2) as x0 eqn:Hx0.
  pose proof seed_bound_hoc3 as Hseed. rewrite <- Hx0 in Hseed. clear Hx0.
  (* Round 2 *)
  remember (iter (ho 3) 2 (hoc 0 3 10) + 2 * 4 + 2) as B2 eqn:HB2.
  assert (HB2_ge : hoc 0 3 10 <= B2).
  { rewrite HB2. cbn [iter].
    pose proof (ho_ge_add4 3 (hoc 0 3 10)).
    pose proof (ho_ge_add4 3 (ho 3 (hoc 0 3 10))). lia. }
  assert (HB2_mod : B2 mod 3 = 1).
  { rewrite HB2. rewrite (Hmod3 _ _ _ (10 + 3 + 2)); [reflexivity |].
    rewrite Hiter_mod, <- Nat.Div0.add_mod_idemp_l, hoc_mod3, Nat.Div0.add_mod_idemp_l. reflexivity. }
  assert (HB2_lb : 3 * (x0 + 6) <= B2) by lia.
  assert (Hk2 : exists k2, B2 = 3 * (k2 + 2) + 1 /\ k2 = B2 / 3 - 2).
  { exists (B2 / 3 - 2). pose proof (Nat.div_mod B2 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B2 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk2 as [k2 [HB2_eq Hk2_eq]].
  (* Round 3 *)
  remember (hoc 0 k2 10 + 2 * (k2 + 1) + 2) as B3 eqn:HB3.
  assert (HB3_mod : B3 mod 3 = 2).
  { rewrite HB3. rewrite (Hmod3 _ _ _ (10 + k2)) by apply hoc_mod3.
    replace (10 + k2 + 2 * (k2 + 1) + 2) with (2 + (k2 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB3_lb : 3 * (iter f_omega_mul2 1 x0 + 6) <= B3).
  { pose proof (hoc_round_step x0 B2 HB2_lb). rewrite <- Hk2_eq in H. cbn [iter]. lia. }
  assert (Hk3 : exists k3, B3 = 3 * (k3 + 1) + 2 /\ B3 / 3 - 2 <= k3).
  { exists (B3 / 3 - 1). pose proof (Nat.div_mod B3 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B3 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk3 as [k3 [HB3_eq Hk3_ge]].
  (* Round 4 *)
  remember (hoc 0 k3 10 + 2 * (k3 + 1) + 2) as B4 eqn:HB4.
  assert (HB4_mod : B4 mod 3 = 2).
  { rewrite HB4. rewrite (Hmod3 _ _ _ (10 + k3)) by apply hoc_mod3.
    replace (10 + k3 + 2 * (k3 + 1) + 2) with (2 + (k3 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB4_lb : 3 * (iter f_omega_mul2 2 x0 + 6) <= B4).
  { pose proof (hoc_round_step (iter f_omega_mul2 1 x0) B3 HB3_lb).
    pose proof (hoc_mono_k (B3 / 3 - 2) k3 0 10 Hk3_ge). rewrite (iter_succ f_omega_mul2 1 x0). lia. }
  assert (Hk4 : exists k4, B4 = 3 * (k4 + 1) + 2 /\ B4 / 3 - 2 <= k4).
  { exists (B4 / 3 - 1). pose proof (Nat.div_mod B4 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B4 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk4 as [k4 [HB4_eq Hk4_ge]].
  (* Round 5 *)
  remember (iter (ho k4) 2 (hoc 0 k4 10) + 2 * (k4 + 1) + 2) as B5 eqn:HB5.
  assert (HB5_ge : hoc 0 k4 10 <= B5).
  { rewrite HB5. cbn [iter].
    pose proof (ho_ge_add4 k4 (hoc 0 k4 10)).
    pose proof (ho_ge_add4 k4 (ho k4 (hoc 0 k4 10))). lia. }
  assert (HB5_mod : B5 mod 3 = 1).
  { rewrite HB5. rewrite (Hmod3 _ _ _ (10 + k4 + 2)).
    - replace (10 + k4 + 2 + 2 * (k4 + 1) + 2) with (1 + (k4 + 5) * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    - rewrite Hiter_mod, <- Nat.Div0.add_mod_idemp_l, hoc_mod3, Nat.Div0.add_mod_idemp_l. reflexivity. }
  assert (HB5_lb : 3 * (iter f_omega_mul2 3 x0 + 6) <= B5).
  { pose proof (hoc_round_step (iter f_omega_mul2 2 x0) B4 HB4_lb).
    pose proof (hoc_mono_k (B4 / 3 - 2) k4 0 10 Hk4_ge).
    rewrite (iter_succ f_omega_mul2 2 x0). lia. }
  assert (Hk5 : exists k5, B5 = 3 * (k5 + 2) + 1 /\ k5 = B5 / 3 - 2).
  { exists (B5 / 3 - 2). pose proof (Nat.div_mod B5 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B5 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk5 as [k5 [HB5_eq Hk5_eq]].
  (* Round 6 *)
  remember (hoc 0 k5 10 + 2 * (k5 + 1) + 2) as B6 eqn:HB6.
  assert (HB6_mod : B6 mod 3 = 2).
  { rewrite HB6. rewrite (Hmod3 _ _ _ (10 + k5)) by apply hoc_mod3.
    replace (10 + k5 + 2 * (k5 + 1) + 2) with (2 + (k5 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB6_lb : 3 * (iter f_omega_mul2 4 x0 + 6) <= B6).
  { pose proof (hoc_round_step (iter f_omega_mul2 3 x0) B5 HB5_lb).
    rewrite <- Hk5_eq in H.
    rewrite (iter_succ f_omega_mul2 3 x0). lia. }
  assert (Hk6 : exists k6, B6 = 3 * (k6 + 1) + 2 /\ B6 / 3 - 2 <= k6).
  { exists (B6 / 3 - 1). pose proof (Nat.div_mod B6 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B6 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk6 as [k6 [HB6_eq Hk6_ge]].
  (* Round 7 *)
  remember (hoc 0 k6 10 + 2 * (k6 + 1) + 2) as B7 eqn:HB7.
  assert (HB7_mod : B7 mod 3 = 2).
  { rewrite HB7. rewrite (Hmod3 _ _ _ (10 + k6)) by apply hoc_mod3.
    replace (10 + k6 + 2 * (k6 + 1) + 2) with (2 + (k6 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB7_lb : 3 * (iter f_omega_mul2 5 x0 + 6) <= B7).
  { pose proof (hoc_round_step (iter f_omega_mul2 4 x0) B6 HB6_lb).
    pose proof (hoc_mono_k (B6 / 3 - 2) k6 0 10 Hk6_ge).
    rewrite (iter_succ f_omega_mul2 4 x0). lia. }
  assert (Hk7 : exists k7, B7 = 3 * (k7 + 1) + 2 /\ B7 / 3 - 2 <= k7).
  { exists (B7 / 3 - 1). pose proof (Nat.div_mod B7 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B7 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk7 as [k7 [HB7_eq Hk7_ge]].
  (* Round 8 *)
  remember (iter (ho k7) 2 (hoc 0 k7 10) + 2 * (k7 + 1) + 2) as B8 eqn:HB8.
  assert (HB8_ge : hoc 0 k7 10 <= B8).
  { rewrite HB8. cbn [iter].
    pose proof (ho_ge_add4 k7 (hoc 0 k7 10)).
    pose proof (ho_ge_add4 k7 (ho k7 (hoc 0 k7 10))). lia. }
  assert (HB8_mod : B8 mod 3 = 1).
  { rewrite HB8. rewrite (Hmod3 _ _ _ (10 + k7 + 2)).
    - replace (10 + k7 + 2 + 2 * (k7 + 1) + 2) with (1 + (k7 + 5) * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    - rewrite Hiter_mod, <- Nat.Div0.add_mod_idemp_l, hoc_mod3, Nat.Div0.add_mod_idemp_l. reflexivity. }
  assert (HB8_lb : 3 * (iter f_omega_mul2 6 x0 + 6) <= B8).
  { pose proof (hoc_round_step (iter f_omega_mul2 5 x0) B7 HB7_lb).
    pose proof (hoc_mono_k (B7 / 3 - 2) k7 0 10 Hk7_ge).
    rewrite (iter_succ f_omega_mul2 5 x0). lia. }
  assert (Hk8 : exists k8, B8 = 3 * (k8 + 2) + 1 /\ k8 = B8 / 3 - 2).
  { exists (B8 / 3 - 2). pose proof (Nat.div_mod B8 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B8 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk8 as [k8 [HB8_eq Hk8_eq]].
  (* Round 9 *)
  remember (hoc 0 k8 10 + 2 * (k8 + 1) + 2) as B9 eqn:HB9.
  assert (HB9_mod : B9 mod 3 = 2).
  { rewrite HB9. rewrite (Hmod3 _ _ _ (10 + k8)) by apply hoc_mod3.
    replace (10 + k8 + 2 * (k8 + 1) + 2) with (2 + (k8 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB9_lb : 3 * (iter f_omega_mul2 7 x0 + 6) <= B9).
  { pose proof (hoc_round_step (iter f_omega_mul2 6 x0) B8 HB8_lb).
    rewrite <- Hk8_eq in H.
    rewrite (iter_succ f_omega_mul2 6 x0). lia. }
  assert (Hk9 : exists k9, B9 = 3 * (k9 + 1) + 2 /\ B9 / 3 - 2 <= k9).
  { exists (B9 / 3 - 1). pose proof (Nat.div_mod B9 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B9 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk9 as [k9 [HB9_eq Hk9_ge]].
  (* Round 10 *)
  remember (hoc 0 k9 10 + 2 * (k9 + 1) + 2) as B10 eqn:HB10.
  assert (HB10_mod : B10 mod 3 = 2).
  { rewrite HB10. rewrite (Hmod3 _ _ _ (10 + k9)) by apply hoc_mod3.
    replace (10 + k9 + 2 * (k9 + 1) + 2) with (2 + (k9 + 4) * 3) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (HB10_lb : 3 * (iter f_omega_mul2 8 x0 + 6) <= B10).
  { pose proof (hoc_round_step (iter f_omega_mul2 7 x0) B9 HB9_lb).
    pose proof (hoc_mono_k (B9 / 3 - 2) k9 0 10 Hk9_ge).
    rewrite (iter_succ f_omega_mul2 7 x0). lia. }
  assert (Hj : exists j, B10 = 3 * j + 2).
  { exists (B10 / 3). pose proof (Nat.div_mod B10 3 ltac:(lia)). lia. }
  destruct Hj as [j HB10_eq].
  assert (Hreach : CanReach bb20_2 initConfig (EX (3 * j + 2) [1; 1; 0; 0; 1])).
  { eapply canReach_trans; [exists 26; exact (jz_boot _ He) |].
    eapply canReach_trans; [exact bb20_2_rf1 |].
    eapply canReach_trans; [exact bb20_2_rf2 |].
    rewrite <- HB2, HB2_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod1 k2 1 []) |].
    rewrite <- HB3, HB3_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod2_0 k3 1 [1]) |].
    rewrite <- HB4, HB4_eq.
    eapply canReach_trans; [exact (bb20_2_rf5 k4) |].
    rewrite <- HB5, HB5_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod1 k5 0 [1]) |].
    rewrite <- HB6, HB6_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod2_0 k6 1 [0; 1]) |].
    rewrite <- HB7, HB7_eq.
    eapply canReach_trans; [exact (bb20_2_rf8 k7) |].
    rewrite <- HB8, HB8_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod1 k8 0 [0; 1]) |].
    rewrite <- HB9, HB9_eq.
    eapply canReach_trans; [exact (bb20_2_rf_mod2_0 k9 1 [0; 0; 1]) |].
    rewrite <- HB10, HB10_eq.
    apply canReach_refl. }
  destruct Hreach as [t1 Ht1].
  destruct (bb20_2_rf11_halt j) as [c [Hc Hst]].
  exists (t1 + (3 * j + 7)). split.
  - exists c. split; [eapply reaches_trans; [exact Ht1 | exact Hc] | exact Hst].
  - lia.
Qed.

Print Assumptions bb20_2_halts_gt_f_omega_mul2_8.
