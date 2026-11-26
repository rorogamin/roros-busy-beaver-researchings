(*
  rocq/BB16_5.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(16, 5):
    TM: 3LG1LA1LG3LA4LA_2RH3RB1LD2RH3LK_3RB1LB3LC2RC1RP_2RE---3LC2RC---_3RB2RE2RE4RF0RI_1LG1RF3LG3RF4LG_2RJ0LA2LG2LI4LK_4LA3LB2RM2RH3LL_2RC1LI3LG3LI4LI_1LP1RJ2RJ3RJ4RF_4LP1LK3LE3LK4LL_3RB1LL1LL1LL---_1RZ4RB0LN4LP2LO_3RB---0LN0LN---_0RC0LK2LO2LO2RP_3RO4LB4LP4LP2RM
    Domain: BB(16, 5) (16 states, 5 symbols)
    Previous best dominated bound: BB(14, 5)
    Proved bound here: ValidTM 16 5 bb16_5 /\ exists t, HaltsIn bb16_5 initConfig t /\ f_omega_omega_plus 4 20 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_8_Peeker Fwpw_5_Ladder.
Import ListNotations.

Definition bb16_5 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 3LG 1LA 1LG 3LA 4LA *)
  | 0, 0 => Some (mkAction 3 DL (Some 6))
  | 0, 1 => Some (mkAction 1 DL (Some 0))
  | 0, 2 => Some (mkAction 1 DL (Some 6))
  | 0, 3 => Some (mkAction 3 DL (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 0))
  (* State B (1): 2RH 3RB 1LD 2RH 3LK *)
  | 1, 0 => Some (mkAction 2 DR (Some 7))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  | 1, 4 => Some (mkAction 3 DL (Some 10))
  (* State C (2): 3RB 1LB 3LC 2RC 1RP *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 1 DR (Some 15))
  (* State D (3): 2RE --- 3LC 2RC --- *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  (* State E (4): 3RB 2RE 2RE 4RF 0RI *)
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 4 => Some (mkAction 0 DR (Some 8))
  (* State F (5): 1LG 1RF 3LG 3RF 4LG *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 6))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 6))
  (* State G (6): 2RJ 0LA 2LG 2LI 4LK *)
  | 6, 0 => Some (mkAction 2 DR (Some 9))
  | 6, 1 => Some (mkAction 0 DL (Some 0))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DL (Some 8))
  | 6, 4 => Some (mkAction 4 DL (Some 10))
  (* State H (7): 4LA 3LB 2RM 2RH 3LL *)
  | 7, 0 => Some (mkAction 4 DL (Some 0))
  | 7, 1 => Some (mkAction 3 DL (Some 1))
  | 7, 2 => Some (mkAction 2 DR (Some 12))
  | 7, 3 => Some (mkAction 2 DR (Some 7))
  | 7, 4 => Some (mkAction 3 DL (Some 11))
  (* State I (8): 2RC 1LI 3LG 3LI 4LI *)
  | 8, 0 => Some (mkAction 2 DR (Some 2))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 3 DL (Some 6))
  | 8, 3 => Some (mkAction 3 DL (Some 8))
  | 8, 4 => Some (mkAction 4 DL (Some 8))
  (* State J (9): 1LP 1RJ 2RJ 3RJ 4RF *)
  | 9, 0 => Some (mkAction 1 DL (Some 15))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): 4LP 1LK 3LE 3LK 4LL *)
  | 10, 0 => Some (mkAction 4 DL (Some 15))
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  | 10, 4 => Some (mkAction 4 DL (Some 11))
  (* State L (11): 3RB 1LL 1LL 1LL --- *)
  | 11, 0 => Some (mkAction 3 DR (Some 1))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* State M (12): 1RZ 4RB 0LN 4LP 2LO *)
  | 12, 0 => Some (mkAction 1 DR None)
  | 12, 1 => Some (mkAction 4 DR (Some 1))
  | 12, 2 => Some (mkAction 0 DL (Some 13))
  | 12, 3 => Some (mkAction 4 DL (Some 15))
  | 12, 4 => Some (mkAction 2 DL (Some 14))
  (* State N (13): 3RB --- 0LN 0LN --- *)
  | 13, 0 => Some (mkAction 3 DR (Some 1))
  | 13, 2 => Some (mkAction 0 DL (Some 13))
  | 13, 3 => Some (mkAction 0 DL (Some 13))
  (* State O (14): 0RC 0LK 2LO 2LO 2RP *)
  | 14, 0 => Some (mkAction 0 DR (Some 2))
  | 14, 1 => Some (mkAction 0 DL (Some 10))
  | 14, 2 => Some (mkAction 2 DL (Some 14))
  | 14, 3 => Some (mkAction 2 DL (Some 14))
  | 14, 4 => Some (mkAction 2 DR (Some 15))
  (* State P (15): 3RO 4LB 4LP 4LP 2RM *)
  | 15, 0 => Some (mkAction 3 DR (Some 14))
  | 15, 1 => Some (mkAction 4 DL (Some 1))
  | 15, 2 => Some (mkAction 4 DL (Some 15))
  | 15, 3 => Some (mkAction 4 DL (Some 15))
  | 15, 4 => Some (mkAction 2 DR (Some 12))
  | _, _ => None
  end.

Lemma bb16_5_valid : ValidTM 16 5 bb16_5.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|sym]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|sym]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb16_5_core : Fwpw_5Core bb16_5 7 1 2 3 4 5 6 0 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb16_5_step_0 : StepF5Odd bb16_5 7 0 f_omega_omega.
Proof.
  apply (w5_stepFOdd_omega_omega bb16_5 7 1 2 3 4 5 6 0 8 9 10 11 0 bb16_5_core).
  apply (w5_base_rewrite bb16_5 7 1 2 3 4 5 6 0 8 9 10 11 0 bb16_5_core eq_refl eq_refl).
Qed.

Lemma bb16_5_rew_22 : forall n x R, 1 <= n ->
  exists t, Reaches bb16_5 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) t.
Proof.
  intros n x R Hn.
  assert (H1 : Reaches bb16_5 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb16_5 7 2 1 (Some 12) _ (2 :: x :: R) eq_refl)).
  assert (H2 : Reaches bb16_5 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  assert (H3 : Reaches bb16_5 (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) (mkCfgR (Some 13) (rep n 3 []) (2 :: 0 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  pose proof (w5_sweep_left_23_ne bb16_5 13 0 n 0 (0 :: x :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb16_5 (mkCfgR (Some 13) [] (0 :: rep (S n) 0 (0 :: 0 :: x :: R))) (mkCfgR (Some 1) [3] (rep (S n) 0 (0 :: 0 :: x :: R))) 1)
    by (apply (w8_step_R bb16_5 13 0 2 (Some 1) [] _ eq_refl)).
  assert (H6 : Reaches bb16_5 (mkCfgR (Some 1) [3] (0 :: rep n 0 (0 :: 0 :: x :: R))) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb16_5 1 0 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma bb16_5_pair_2 : StepF5Odd_pair_ne bb16_5 7 2 (f_omega_omega_plus 1).
Proof.
  exact (StepF5Odd_pair_ne_from_sym bb16_5 7 2 0 f_omega_omega f_omega_omega_props bb16_5_step_0 bb16_5_rew_22).
Qed.

Lemma bb16_5_rew_24 : forall n R, 1 <= n -> Nat.Odd n ->
  exists t, Reaches bb16_5 (H5cfg 7 n 1 (2 :: 4 :: R)) (H5cfg 7 1 1 (rep (n + 2) 2 R)) t.
Proof.
  intros n R Hn Ho.
  assert (H1 : Reaches bb16_5 (H5cfg 7 n 1 (2 :: 4 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb16_5 7 2 1 (Some 12) _ (4 :: R) eq_refl)).
  assert (H2 : Reaches bb16_5 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  assert (H3 : Reaches bb16_5 (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) (mkCfgR (Some 14) (rep n 3 []) (2 :: 2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb16_5 14 1 n (2 :: 2 :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb16_5 (mkCfgR (Some 14) [] (0 :: rep (S n) 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb16_5 (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H7 : Reaches bb16_5 (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H8 : Reaches bb16_5 (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) (H5cfg 7 1 1 (rep (n + 2) 2 R)) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb16_5 1 3 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8].
Qed.

Lemma bb16_5_peeker_24 : StepF5Odd_peeker bb16_5 7 2 4 (f_omega_omega_plus 2).
Proof.
  exact (StepF5Odd_peeker_from_pair bb16_5 7 2 4 (f_omega_omega_plus 1)
           (fPlus_props _ f_omega_omega_props 1) (f_omega_omega_plus_ge_2n 1) bb16_5_pair_2 bb16_5_rew_24).
Qed.

Lemma bb16_5_rew_23 : forall n R, 1 <= n -> Nat.Odd n ->
  exists t, Reaches bb16_5 (H5cfg 7 n 1 (2 :: 3 :: R)) (H5cfg 7 1 1 (2 :: 2 :: 2 :: rep n 4 R)) t.
Proof.
  intros n R Hn Ho.
  assert (H1 : Reaches bb16_5 (H5cfg 7 n 1 (2 :: 3 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (3 :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb16_5 7 2 1 (Some 12) _ (3 :: R) eq_refl)).
  assert (H2 : Reaches bb16_5 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (3 :: R)) (mkCfgR (Some 15) (2 :: rep n 3 []) (2 :: 4 :: R)) 1)
    by (apply steps_one; reflexivity).
  assert (H3 : Reaches bb16_5 (mkCfgR (Some 15) (2 :: rep n 3 []) (2 :: 4 :: R)) (mkCfgR (Some 15) (rep n 3 []) (2 :: 4 :: 4 :: R)) 1)
    by (apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb16_5 15 3 n (4 :: 4 :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb16_5 (mkCfgR (Some 15) [] (0 :: rep (S n) 4 (4 :: 4 :: R))) (mkCfgR (Some 14) [3] (rep (S n) 4 (4 :: 4 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb16_5 (mkCfgR (Some 14) [3] (4 :: rep n 4 (4 :: 4 :: R))) (mkCfgR (Some 15) [2; 3] (4 :: 4 :: rep n 4 R)) 1)
    by (rewrite !rep_r8; apply (w8_step_R bb16_5 14 4 1 (Some 15) [3] _ eq_refl)).
  assert (H7 : Reaches bb16_5 (mkCfgR (Some 15) [2; 3] (4 :: 4 :: rep n 4 R)) (mkCfgR (Some 12) [2; 2; 3] (4 :: rep n 4 R)) 1)
    by (apply (w8_step_R bb16_5 15 4 1 (Some 12) [2; 3] _ eq_refl)).
  assert (H8 : Reaches bb16_5 (mkCfgR (Some 12) [2; 2; 3] (4 :: rep n 4 R)) (mkCfgR (Some 14) [2; 3] (2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H9 : Reaches bb16_5 (mkCfgR (Some 14) [2; 3] (2 :: 2 :: rep n 4 R)) (mkCfgR (Some 14) [3] (2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H10 : Reaches bb16_5 (mkCfgR (Some 14) [3] (2 :: 2 :: 2 :: rep n 4 R)) (mkCfgR (Some 14) [] (3 :: 2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H11 : Reaches bb16_5 (mkCfgR (Some 14) [] (3 :: 2 :: 2 :: 2 :: rep n 4 R)) (mkCfgR (Some 14) [] (0 :: 2 :: 2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H12 : Reaches bb16_5 (mkCfgR (Some 14) [] (0 :: 2 :: 2 :: 2 :: 2 :: rep n 4 R)) (mkCfgR (Some 2) [] (2 :: 2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H13 : Reaches bb16_5 (mkCfgR (Some 2) [] (2 :: 2 :: 2 :: 2 :: rep n 4 R)) (mkCfgR (Some 2) [] (0 :: 3 :: 2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H14 : Reaches bb16_5 (mkCfgR (Some 2) [] (0 :: 3 :: 2 :: 2 :: 2 :: rep n 4 R)) (mkCfgR (Some 1) [3] (3 :: 2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (apply steps_one; reflexivity).
  assert (H15 : Reaches bb16_5 (mkCfgR (Some 1) [3] (3 :: 2 :: 2 :: 2 :: rep n 4 R)) (H5cfg 7 1 1 (2 :: 2 :: 2 :: rep n 4 R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb16_5 1 3 1 (Some 7) [3] _ eq_refl)).
  exists (1 + 1 + 1 + S n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8] | exact H9] | exact H10] | exact H11] | exact H12] | exact H13] | exact H14] | exact H15].
Qed.

Lemma bb16_5_peeker_23 : StepF5Odd_peeker bb16_5 7 2 3 (f_omega_omega_plus 3).
Proof.
  exact (StepF5Odd_peeker_from_triple bb16_5 7 2 3 4 (f_omega_omega_plus 1) (f_omega_omega_plus 2)
           (fPlus_props _ f_omega_omega_props 2) bb16_5_pair_2 bb16_5_peeker_24 bb16_5_rew_23).
Qed.

Lemma bb16_5_init :
  Reaches bb16_5 initConfig (H5cfg 7 1 2 (1 :: 4 :: 0 :: 0 :: 2 :: rep 20 3 [])) 359.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB16_5_champion :
  ValidTM 16 5 bb16_5 /\
  exists t, HaltsIn bb16_5 initConfig t /\ f_omega_omega_plus 4 20 < t.
Proof.
  split; [exact bb16_5_valid |].
  pose proof bb16_5_init as H0.
  destruct (w5_init_14_odd bb16_5 7 1 2 3 4 5 6 0 8 9 10 11 bb16_5_core (0 :: 0 :: 2 :: rep 20 3 [])) as [n1 [t1 [H1 [Hn1 [_ Ho1]]]]].
  destruct (bb16_5_step_0 n1 (0 :: 2 :: rep 20 3 []) ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (bb16_5_step_0 n2 (2 :: rep 20 3 []) ltac:(lia) Ho2) as [n3 [t3 [H3 [Hinc3 [_ [_ Ho3]]]]]].
  destruct (StepF5Odd_peeker_rep bb16_5 7 2 3 (f_omega_omega_plus 3) (fPlus_props _ f_omega_omega_props 3) bb16_5_peeker_23 20 n3 [] ltac:(lia) Ho3)
    as [n4 [t4 [H4 [Hinc4 [Hf4 [Ht4 _]]]]]].
  assert (Hhalt1 : Reaches bb16_5 (H5cfg 7 n4 1 [2]) (mkCfgR (Some 12) (2 :: 2 :: rep n4 3 []) []) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  assert (Hhalt2 : Reaches bb16_5 (mkCfgR (Some 12) (2 :: 2 :: rep n4 3 []) []) (mkCfgR None (1 :: 2 :: 2 :: rep n4 3 []) []) 1)
    by (apply steps_one; reflexivity).
  exists (359 + t1 + t2 + t3 + t4 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: 2 :: rep n4 3 []) []). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4] | exact Hhalt1] | exact Hhalt2].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf4 20 ltac:(lia) ltac:(lia)) as Hc.
    specialize (Ht4 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB16_5_champion.
