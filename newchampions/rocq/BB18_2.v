(*
  rocq/BB18_2.v
  18-state, 2-symbol Busy Beaver champion:
    ValidTM 18 2 bb18_2  /\  exists s, HaltsIn bb18_2 initConfig s /\ iter f_omega_mul2 2 (fFin 5 2) < s
  Strictly beats the bbchallenge wiki BB(18) champion (> f_{ω×2}(f_{ω+1}(f_4(2)))).

  Uses the shared 15-state Jacobzheng f_{ω×2} engine (rocq/Jacobzheng.v)
  with exit transitions J0=1LQ, K0=1RZ, L0=1LH.
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz JZMath Jacobzheng.
Import ListNotations.

Definition bb18_2 : TM := fun s sym =>
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
  | 9,  0 => Some (mkAction 1 DL (Some 16))  (* J0: 1LQ *)
  | 9,  1 => Some (mkAction 0 DR (Some 10))  (* J1: 0RK *)
  | 10, 0 => Some (mkAction 1 DR None)       (* K0: 1RZ *)
  | 10, 1 => Some (mkAction 1 DR (Some 11))  (* K1: 1RL *)
  | 11, 0 => Some (mkAction 1 DL (Some 7))   (* L0: 1LH *)
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
  | _,  _ => None
  end.

Lemma bb18_2_valid : ValidTM 18 2 bb18_2.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 18 (destruct s as [| s]; [
      do 2 (destruct sym as [| sym]; [simpl; lia |]); lia
    |]); lia.
  - do 18 (destruct s as [| s]; [
      do 2 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb18_2_engine : JZEngine bb18_2.
Proof. constructor; reflexivity. Qed.

Local Lemma bb18_2_J0 : bb18_2 9 0 = Some (mkAction 1 DL (Some 16)). Proof. reflexivity. Qed.
Local Lemma bb18_2_K0 : bb18_2 10 0 = Some (mkAction 1 DR None). Proof. reflexivity. Qed.

Local Lemma bb18_2_rf1 : CanReach bb18_2 (EX 5 []) (EX 14 [1; 1]).
Proof.
  pose proof bb18_2_engine as He.
  assert (H1 : Reaches bb18_2 (EX 5 []) (mkCfgR (Some 9) [0; 1; 1; 0; 0; 1] [1; 1; 1]) 16)
    by reflexivity.
  assert (H2 : Reaches bb18_2 (mkCfgR (Some 9) [0; 1; 1; 0; 0; 1] [1; 1; 1])
                              (mkCfgR (Some 12) [1] [0; 1; 0; 0; 1; 0; 0; 1; 1]) 25)
    by reflexivity.
  eapply canReach_trans; [exists 16; exact H1 |].
  eapply canReach_trans; [exists 25; exact H2 |].
  eapply canReach_trans; [apply (jz_M_finish _ He) |].
  eapply canReach_trans; [apply (rule_CI_11 _ He) |].
  eapply canReach_trans; [apply (rule_CI_10 _ He 7 [0; 1; 0; 0; 1; 1]) |].
  eapply canReach_trans; [apply (rule_SW_0 _ He 0 7 [1; 0; 0; 1; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He 0 10 [0; 1; 1]) |].
  apply (rule_CO_0 _ He 1 10 [1; 1]).
Qed.

Local Lemma bb18_2_rf2 :
  CanReach bb18_2 (EX 14 [1; 1]) (EX (hoc 0 4 10 + 2 * 4 + 2) [1; 0; 0; 1; 1]).
Proof.
  pose proof bb18_2_engine as He.
  assert (H1 : Reaches bb18_2 (EX 14 [1; 1])
                              (mkCfgR (Some 9) (0 :: rep110 4 [0; 1]) [1; 1; 1; 1; 1]) 29)
    by reflexivity.
  assert (H2 : Reaches bb18_2 (mkCfgR (Some 9) (0 :: rep110 4 [0; 1]) [1; 1; 1; 1; 1])
                              (mkCfgR (Some 12) (rep110 4 [0; 1]) [0; 1; 0; 0; 1; 0; 0; 1; 1]) 41)
    by reflexivity.
  eapply canReach_trans; [exists 29; exact H1 |].
  eapply canReach_trans; [exists 41; exact H2 |].
  eapply canReach_trans; [exists 12; exact (jz_M_loop _ He 4 [0; 1] [1; 0; 0; 1; 0; 0; 1; 1]) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B1 _ He) | simp_cons0; simpl rep101].
  eapply canReach_trans;
    [exists 3; exact (loop_NOP _ He 1 1 [] (0 :: 1 :: rep101 3 [1; 0; 0; 1; 0; 0; 1; 1])) |].
  simpl rep110.
  eapply canReach_step; [eapply step_L_cons; apply (jz_N0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [apply (jz_M_finish _ He) |].
  eapply canReach_trans; [apply (rule_CI_11 _ He) |].
  eapply canReach_trans; [apply (rule_CI_10 _ He 7 (0 :: 1 :: rep101 3 [1; 0; 0; 1; 0; 0; 1; 1])) |].
  eapply canReach_trans; [apply (rule_SW_0 _ He 0 7 (1 :: rep101 3 [1; 0; 0; 1; 0; 0; 1; 1])) |].
  assert (Hrl : 1 :: rep101 3 [1; 0; 0; 1; 0; 0; 1; 1] =
                rl (rep 4 2 []) [0; 1; 0; 0; 1; 1]) by reflexivity.
  rewrite Hrl.
  eapply canReach_trans; [apply (CO_chain _ He 4 0 10) | rewrite Nat.add_0_l].
  apply (rule_CO_0 _ He 4 (hoc 0 4 10) [1; 0; 0; 1; 1]).
Qed.

Local Lemma bb18_2_rf_mod0 : forall k R',
  CanReach bb18_2 (EX (3 * (k + 2)) (1 :: R'))
                  (CO 0 10 (rl (rep k 2 []) (1 :: 0 :: 1 :: 1 :: 1 :: R'))).
Proof.
  intros k R'. pose proof bb18_2_engine as He. unfold EX. simp_cons0.
  eapply canReach_trans; [exists (3 * (k + 2)); exact (jz_triJKL _ He (k + 2) 0 [1] (0 :: 1 :: R')) |].
  replace (k + 2) with (S (k + 1)) by lia. simpl rep110.
  eapply canReach_step; [eapply step_L_cons; apply bb18_2_J0 | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_Q1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_trans; [exists (3 * (k + 1)); exact (jz_M_loop _ He (k + 1) [0; 1] (0 :: 1 :: 1 :: 1 :: R')) |].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_R_cons; apply (jz_B1 _ He) | simp_cons0].
  replace (k + 1) with (S k) by lia. simpl rep101.
  eapply canReach_trans; [exists 3; exact (loop_NOP _ He 1 1 [] (0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R'))) |].
  simpl rep110.
  eapply canReach_step; [eapply step_L_cons; apply (jz_N0 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_A1 _ He) | simp_cons0].
  eapply canReach_step; [eapply step_L_cons; apply (jz_M1 _ He) | simp_cons0].
  eapply canReach_trans; [apply (jz_M_finish _ He) |].
  eapply canReach_trans; [apply (rule_CI_11 _ He) |].
  eapply canReach_trans; [apply (rule_CI_10 _ He 7 (0 :: 1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R'))) |].
  eapply canReach_trans; [apply (rule_SW_0 _ He 0 7 (1 :: rep101 k (0 :: 1 :: 1 :: 1 :: R'))) |].
  rewrite one_rep101_eq_rl.
  apply canReach_refl.
Qed.

Local Lemma bb18_2_rf3 : forall k,
  CanReach bb18_2 (EX (3 * (k + 2)) [1; 0; 0; 1; 1])
                  (EX (iter (ho (k + 1)) 2 (hoc 0 k 10) + 2 * (k + 2) + 2) [1; 1]).
Proof.
  intro k. pose proof bb18_2_engine as He.
  eapply canReach_trans; [apply bb18_2_rf_mod0 |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (rule_CO_10 _ He k (hoc 0 k 10) [1; 1; 1; 0; 0; 1; 1]) |].
  replace (S k) with (k + 1) by lia.
  eapply canReach_trans; [apply (CO_iter _ He 2 (k + 1) (hoc 0 k 10) [0; 0; 1; 1]) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He (k + 1) _ [0; 1; 1]) |].
  replace (S (k + 1)) with (k + 2) by lia.
  apply (rule_CO_0 _ He (k + 2) _ [1; 1]).
Qed.

Local Lemma bb18_2_rf4 : forall k,
  CanReach bb18_2 (EX (3 * (k + 2)) [1; 1])
                  (EX (iter (ho (k + 1)) 3 (hoc 0 k 10) + 2 * (k + 2) + 2) []).
Proof.
  intro k. pose proof bb18_2_engine as He.
  eapply canReach_trans; [apply bb18_2_rf_mod0 |].
  eapply canReach_trans; [apply (CO_chain _ He k 0 10) | rewrite Nat.add_0_l].
  eapply canReach_trans; [apply (rule_CO_10 _ He k (hoc 0 k 10) [1; 1; 1; 1]) |].
  replace (S k) with (k + 1) by lia.
  eapply canReach_trans; [apply (CO_iter _ He 3 (k + 1) (hoc 0 k 10) []) |].
  eapply canReach_trans; [apply (rule_CO_10 _ He (k + 1) _ []) |].
  replace (S (k + 1)) with (k + 2) by lia.
  apply (rule_CO_0 _ He (k + 2) _ []).
Qed.

Local Lemma bb18_2_rf5_halt : forall j,
  exists c, Reaches bb18_2 (EX (3 * j + 1) []) c (3 * j + 2) /\ cfg_st c = None.
Proof.
  intro j. pose proof bb18_2_engine as He. unfold EX. simpl cons0.
  assert (Hsplit : rep (3 * j + 1) 1 [] = rep (3 * j) 1 [1]).
  { rewrite <- rep_add_sym. reflexivity. }
  rewrite Hsplit.
  pose proof (jz_triJKL _ He j 0 [1] [1]) as H1.
  pose proof (reaches_one _ _ _ (step_R_cons _ _ _ _ _ (rep110 j [0; 1]) [] (jz_J1 _ He))) as H2.
  pose proof (reaches_one _ _ _ (step_R_zero _ _ _ _ (cons0 0 (rep110 j [0; 1])) [] bb18_2_K0)) as H3.
  eexists. split.
  - replace (3 * j + 2) with (3 * j + 1 + 1) by lia.
    eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  - reflexivity.
Qed.

Theorem bb18_2_halts_gt_f_omega_mul2_2 :
  ValidTM 18 2 bb18_2 /\
  exists s, HaltsIn bb18_2 initConfig s /\ iter f_omega_mul2 2 (fFin 5 2) < s.
Proof.
  split; [exact bb18_2_valid |].
  pose proof bb18_2_engine as He.
  remember (hoc 0 4 10 + 2 * 4 + 2) as B2 eqn:HB2.
  assert (HB2_mod : B2 mod 3 = 0).
  { subst B2.
    rewrite <- (Nat.Div0.add_mod_idemp_l (hoc 0 4 10 + 2 * 4) 2 3).
    rewrite <- (Nat.Div0.add_mod_idemp_l (hoc 0 4 10) (2 * 4) 3).
    rewrite hoc_mod3. reflexivity. }
  assert (HB2_lb : 3 * (fFin 5 2 + 6) <= B2).
  { pose proof seed_bound_hoc3. pose proof (hoc_mono_k 3 4 0 10 ltac:(lia)). lia. }
  assert (Hk2 : exists k2, B2 = 3 * (k2 + 2) /\ k2 = B2 / 3 - 2).
  { exists (B2 / 3 - 2).
    pose proof (Nat.div_mod B2 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B2 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk2 as [k2 [HB2_eq Hk2_eq]].
  remember (iter (ho (k2 + 1)) 2 (hoc 0 k2 10) + 2 * (k2 + 2) + 2) as B3 eqn:HB3.
  assert (HB3_ge : hoc 0 k2 10 <= B3).
  { rewrite HB3. simpl iter.
    pose proof (ho_ge_add4 (k2 + 1) (hoc 0 k2 10)).
    pose proof (ho_ge_add4 (k2 + 1) (ho (k2 + 1) (hoc 0 k2 10))). lia. }
  assert (Hiter_mod : forall m k x, iter (ho m) k x mod 3 = (x + k) mod 3).
  { intros m k. induction k as [| p IH]; intro x; cbn [iter].
    - replace (x + 0) with x by lia. reflexivity.
    - rewrite ho_mod3, <- Nat.Div0.add_mod_idemp_l, IH, Nat.Div0.add_mod_idemp_l.
      f_equal. lia. }
  assert (Hmod3 : forall a b c d, a mod 3 = d mod 3 -> (a + b + c) mod 3 = (d + b + c) mod 3).
  { intros a b c d H.
    rewrite Nat.Div0.add_mod, (Nat.Div0.add_mod a b 3), H,
            <- (Nat.Div0.add_mod d b 3), <- Nat.Div0.add_mod. reflexivity. }
  assert (HB3_mod : B3 mod 3 = 0).
  { rewrite HB3.
    rewrite (Hmod3 _ _ _ (10 + k2 + 2)).
    - replace (10 + k2 + 2 + 2 * (k2 + 2) + 2) with (0 + (k2 + 6) * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    - rewrite Hiter_mod, <- Nat.Div0.add_mod_idemp_l, hoc_mod3, Nat.Div0.add_mod_idemp_l.
      reflexivity. }
  assert (HB3_lb : 3 * (f_omega_mul2 (fFin 5 2) + 6) <= B3).
  { pose proof (hoc_round_step (fFin 5 2) B2 HB2_lb). rewrite <- Hk2_eq in H. lia. }
  assert (Hk3 : exists k3, B3 = 3 * (k3 + 2) /\ k3 = B3 / 3 - 2).
  { exists (B3 / 3 - 2).
    pose proof (Nat.div_mod B3 3 ltac:(lia)).
    pose proof (Nat.div_le_lower_bound B3 3 6 ltac:(lia) ltac:(lia)). lia. }
  destruct Hk3 as [k3 [HB3_eq Hk3_eq]].
  remember (iter (ho (k3 + 1)) 3 (hoc 0 k3 10) + 2 * (k3 + 2) + 2) as B4 eqn:HB4.
  assert (HB4_ge : hoc 0 k3 10 <= B4).
  { rewrite HB4. simpl iter.
    pose proof (ho_ge_add4 (k3 + 1) (hoc 0 k3 10)).
    pose proof (ho_ge_add4 (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10))).
    pose proof (ho_ge_add4 (k3 + 1) (ho (k3 + 1) (ho (k3 + 1) (hoc 0 k3 10)))). lia. }
  assert (HB4_mod : B4 mod 3 = 1).
  { rewrite HB4.
    rewrite (Hmod3 _ _ _ (10 + k3 + 3)).
    - replace (10 + k3 + 3 + 2 * (k3 + 2) + 2) with (1 + (k3 + 6) * 3) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    - rewrite Hiter_mod, <- Nat.Div0.add_mod_idemp_l, hoc_mod3, Nat.Div0.add_mod_idemp_l.
      reflexivity. }
  assert (HB4_lb : 3 * (f_omega_mul2 (f_omega_mul2 (fFin 5 2)) + 6) <= B4).
  { pose proof (hoc_round_step (f_omega_mul2 (fFin 5 2)) B3 HB3_lb). rewrite <- Hk3_eq in H. lia. }
  assert (Hj : exists j, B4 = 3 * j + 1).
  { exists (B4 / 3). pose proof (Nat.div_mod B4 3 ltac:(lia)). lia. }
  destruct Hj as [j HB4_eq].
  assert (Hreach : CanReach bb18_2 initConfig (EX (3 * j + 1) [])).
  { eapply canReach_trans; [exists 26; exact (jz_boot _ He) |].
    eapply canReach_trans; [exact bb18_2_rf1 |].
    eapply canReach_trans; [exact bb18_2_rf2 |].
    rewrite <- HB2, HB2_eq.
    eapply canReach_trans; [exact (bb18_2_rf3 k2) |].
    rewrite <- HB3, HB3_eq.
    eapply canReach_trans; [exact (bb18_2_rf4 k3) |].
    rewrite <- HB4, HB4_eq.
    apply canReach_refl. }
  destruct Hreach as [t1 Ht1].
  destruct (bb18_2_rf5_halt j) as [c [Hc Hst]].
  exists (t1 + (3 * j + 2)). split.
  - exists c. split; [eapply reaches_trans; [exact Ht1 | exact Hc] | exact Hst].
  - simpl iter. lia.
Qed.

Print Assumptions bb18_2_halts_gt_f_omega_mul2_2.
