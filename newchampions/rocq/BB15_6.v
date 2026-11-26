(*
  rocq/BB15_6.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(15, 6):
    TM: 1RJ1LA1LG3LA4LA---_2RH3RB1LD2RH3LJ---_3RB1LB3LC2RC0LN---_2RE---3LC2RC---4RG_3RB2RE2RE4RF1LL---_1LG1RF3LG3RF4LG---_2RJ0LA2LG2LI4LK0RM_4LA3LB2RM2RH3LL---_2RC1LI3LG3LI4LI---_4RI1RJ2RJ3RJ4RF---_0RG1LK3LE3LK------_3RB1LL1LL1LL------_1RZ4RC0LN---2LO---_3RB---0LN0LN5RB---_0RC---2LO2LO------
    Domain: BB(15, 6) (15 states, 6 symbols)
    Previous best dominated bound: BB(12, 6)
    Proved bound here: ValidTM 15 6 bb15_6 /\ exists t, HaltsIn bb15_6 initConfig t /\ f_omega_omega_plus 3 35 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_8_Peeker Fwpw_5_Ladder.
Import ListNotations.

Definition bb15_6 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1RJ 1LA 1LG 3LA 4LA --- *)
  | 0, 0 => Some (mkAction 1 DR (Some 9))
  | 0, 1 => Some (mkAction 1 DL (Some 0))
  | 0, 2 => Some (mkAction 1 DL (Some 6))
  | 0, 3 => Some (mkAction 3 DL (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 0))
  (* State B (1): 2RH 3RB 1LD 2RH 3LJ --- *)
  | 1, 0 => Some (mkAction 2 DR (Some 7))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  | 1, 4 => Some (mkAction 3 DL (Some 9))
  (* State C (2): 3RB 1LB 3LC 2RC 0LN --- *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 0 DL (Some 13))
  (* State D (3): 2RE --- 3LC 2RC --- 4RG *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 5 => Some (mkAction 4 DR (Some 6))
  (* State E (4): 3RB 2RE 2RE 4RF 1LL --- *)
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 4 => Some (mkAction 1 DL (Some 11))
  (* State F (5): 1LG 1RF 3LG 3RF 4LG --- *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 6))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 6))
  (* State G (6): 2RJ 0LA 2LG 2LI 4LK 0RM *)
  | 6, 0 => Some (mkAction 2 DR (Some 9))
  | 6, 1 => Some (mkAction 0 DL (Some 0))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DL (Some 8))
  | 6, 4 => Some (mkAction 4 DL (Some 10))
  | 6, 5 => Some (mkAction 0 DR (Some 12))
  (* State H (7): 4LA 3LB 2RM 2RH 3LL --- *)
  | 7, 0 => Some (mkAction 4 DL (Some 0))
  | 7, 1 => Some (mkAction 3 DL (Some 1))
  | 7, 2 => Some (mkAction 2 DR (Some 12))
  | 7, 3 => Some (mkAction 2 DR (Some 7))
  | 7, 4 => Some (mkAction 3 DL (Some 11))
  (* State I (8): 2RC 1LI 3LG 3LI 4LI --- *)
  | 8, 0 => Some (mkAction 2 DR (Some 2))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 3 DL (Some 6))
  | 8, 3 => Some (mkAction 3 DL (Some 8))
  | 8, 4 => Some (mkAction 4 DL (Some 8))
  (* State J (9): 4RI 1RJ 2RJ 3RJ 4RF --- *)
  | 9, 0 => Some (mkAction 4 DR (Some 8))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): 0RG 1LK 3LE 3LK --- --- *)
  | 10, 0 => Some (mkAction 0 DR (Some 6))
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  (* State L (11): 3RB 1LL 1LL 1LL --- --- *)
  | 11, 0 => Some (mkAction 3 DR (Some 1))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* State M (12): 1RZ 4RC 0LN --- 2LO --- *)
  | 12, 0 => Some (mkAction 1 DR None)
  | 12, 1 => Some (mkAction 4 DR (Some 2))
  | 12, 2 => Some (mkAction 0 DL (Some 13))
  | 12, 4 => Some (mkAction 2 DL (Some 14))
  (* State N (13): 3RB --- 0LN 0LN 5RB --- *)
  | 13, 0 => Some (mkAction 3 DR (Some 1))
  | 13, 2 => Some (mkAction 0 DL (Some 13))
  | 13, 3 => Some (mkAction 0 DL (Some 13))
  | 13, 4 => Some (mkAction 5 DR (Some 1))
  (* State O (14): 0RC --- 2LO 2LO --- --- *)
  | 14, 0 => Some (mkAction 0 DR (Some 2))
  | 14, 2 => Some (mkAction 2 DL (Some 14))
  | 14, 3 => Some (mkAction 2 DL (Some 14))
  | _, _ => None
  end.

Lemma bb15_6_valid : ValidTM 15 6 bb15_6.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|sym]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|sym]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb15_6_core : Fwpw_5Core bb15_6 7 1 2 3 4 5 6 0 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb15_6_step_0 : StepF5Odd bb15_6 7 0 f_omega_omega.
Proof.
  apply (w5_stepFOdd_omega_omega bb15_6 7 1 2 3 4 5 6 0 8 9 10 11 0 bb15_6_core).
  apply (w5_base_rewrite bb15_6 7 1 2 3 4 5 6 0 8 9 10 11 0 bb15_6_core eq_refl eq_refl).
Qed.

Lemma bb15_6_rew_22 : forall n x R, 1 <= n ->
  exists t, Reaches bb15_6 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) t.
Proof.
  intros n x R Hn.
  assert (H1 : Reaches bb15_6 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb15_6 7 2 1 (Some 12) _ (2 :: x :: R) eq_refl)).
  assert (H2 : Reaches bb15_6 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  assert (H3 : Reaches bb15_6 (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) (mkCfgR (Some 13) (rep n 3 []) (2 :: 0 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  pose proof (w5_sweep_left_23_ne bb15_6 13 0 n 0 (0 :: x :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb15_6 (mkCfgR (Some 13) [] (0 :: rep (S n) 0 (0 :: 0 :: x :: R))) (mkCfgR (Some 1) [3] (rep (S n) 0 (0 :: 0 :: x :: R))) 1)
    by (apply (w8_step_R bb15_6 13 0 2 (Some 1) [] _ eq_refl)).
  assert (H6 : Reaches bb15_6 (mkCfgR (Some 1) [3] (0 :: rep n 0 (0 :: 0 :: x :: R))) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb15_6 1 0 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma bb15_6_pair_2 : StepF5Odd_pair_ne bb15_6 7 2 (f_omega_omega_plus 1).
Proof.
  exact (StepF5Odd_pair_ne_from_sym bb15_6 7 2 0 f_omega_omega f_omega_omega_props bb15_6_step_0 bb15_6_rew_22).
Qed.

Lemma bb15_6_rew_24 : forall n R, 1 <= n -> Nat.Odd n ->
  exists t, Reaches bb15_6 (H5cfg 7 n 1 (2 :: 4 :: R)) (H5cfg 7 1 1 (rep (n + 2) 2 R)) t.
Proof.
  intros n R Hn Ho.
  assert (H1 : Reaches bb15_6 (H5cfg 7 n 1 (2 :: 4 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb15_6 7 2 1 (Some 12) _ (4 :: R) eq_refl)).
  assert (H2 : Reaches bb15_6 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  assert (H3 : Reaches bb15_6 (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) (mkCfgR (Some 14) (rep n 3 []) (2 :: 2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb15_6 14 1 n (2 :: 2 :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb15_6 (mkCfgR (Some 14) [] (0 :: rep (S n) 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb15_6 (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H7 : Reaches bb15_6 (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H8 : Reaches bb15_6 (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) (H5cfg 7 1 1 (rep (n + 2) 2 R)) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb15_6 1 3 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8].
Qed.

Lemma bb15_6_peeker_24 : StepF5Odd_peeker bb15_6 7 2 4 (f_omega_omega_plus 2).
Proof.
  exact (StepF5Odd_peeker_from_pair bb15_6 7 2 4 (f_omega_omega_plus 1)
           (fPlus_props _ f_omega_omega_props 1) (f_omega_omega_plus_ge_2n 1) bb15_6_pair_2 bb15_6_rew_24).
Qed.

Lemma bb15_6_init :
  Reaches bb15_6 initConfig (H5cfg 7 1 2 (1 :: 4 :: 2 :: rep 35 4 [])) 902.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB15_6_champion :
  ValidTM 15 6 bb15_6 /\
  exists t, HaltsIn bb15_6 initConfig t /\ f_omega_omega_plus 3 35 < t.
Proof.
  split; [exact bb15_6_valid |].
  pose proof bb15_6_init as H0.
  destruct (w5_init_14_odd bb15_6 7 1 2 3 4 5 6 0 8 9 10 11 bb15_6_core (2 :: rep 35 4 [])) as [n1 [t1 [H1 [Hn1 [_ Ho1]]]]].
  destruct (StepF5Odd_peeker_rep bb15_6 7 2 4 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) bb15_6_peeker_24 35 n1 [] ltac:(lia) Ho1)
    as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 _]]]]]].
  assert (Hhalt1 : Reaches bb15_6 (H5cfg 7 n2 1 [2]) (mkCfgR (Some 12) (2 :: 2 :: rep n2 3 []) []) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  assert (Hhalt2 : Reaches bb15_6 (mkCfgR (Some 12) (2 :: 2 :: rep n2 3 []) []) (mkCfgR None (1 :: 2 :: 2 :: rep n2 3 []) []) 1)
    by (apply steps_one; reflexivity).
  exists (902 + t1 + t2 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: 2 :: rep n2 3 []) []). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact Hhalt1] | exact Hhalt2].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf2 35 ltac:(lia) ltac:(lia)) as Hc.
    specialize (Ht2 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB15_6_champion.
