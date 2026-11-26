(*
  rocq/BB15_5.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(15, 5):
    TM: 2RG1LA1LG3LA4LA_2RH3RB1LD2RH---_3RB1LB3LC2RC4RH_2RE---3LC2RC---_3RB2RE2RE4RF---_1LG1RF3LG3RF4LG_2RJ0LA2LG2LI4LK_4LA3LB2RM2RH3LL_2RC1LI3LG3LI4LI_0RK1RJ2RJ3RJ4RF_2LH1LK3LE3LK---_3RB1LL1LL1LL---_1RZ4LJ0LN---2LO_3RB---0LN0LN---_0RC---2LO2LO2LD
    Domain: BB(15, 5) (15 states, 5 symbols)
    Previous best dominated bound: BB(14, 5)
    Proved bound here: ValidTM 15 5 bb15_5 /\ exists t, HaltsIn bb15_5 initConfig t /\ f_omega_omega_plus 3 27 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_8_Peeker Fwpw_5_Ladder.
Import ListNotations.

Definition bb15_5 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2RG 1LA 1LG 3LA 4LA *)
  | 0, 0 => Some (mkAction 2 DR (Some 6))
  | 0, 1 => Some (mkAction 1 DL (Some 0))
  | 0, 2 => Some (mkAction 1 DL (Some 6))
  | 0, 3 => Some (mkAction 3 DL (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 0))
  (* State B (1): 2RH 3RB 1LD 2RH --- *)
  | 1, 0 => Some (mkAction 2 DR (Some 7))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  (* State C (2): 3RB 1LB 3LC 2RC 4RH *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DR (Some 7))
  (* State D (3): 2RE --- 3LC 2RC --- *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  (* State E (4): 3RB 2RE 2RE 4RF --- *)
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
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
  (* State J (9): 0RK 1RJ 2RJ 3RJ 4RF *)
  | 9, 0 => Some (mkAction 0 DR (Some 10))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): 2LH 1LK 3LE 3LK --- *)
  | 10, 0 => Some (mkAction 2 DL (Some 7))
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  (* State L (11): 3RB 1LL 1LL 1LL --- *)
  | 11, 0 => Some (mkAction 3 DR (Some 1))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* State M (12): 1RZ 4LJ 0LN --- 2LO *)
  | 12, 0 => Some (mkAction 1 DR None)
  | 12, 1 => Some (mkAction 4 DL (Some 9))
  | 12, 2 => Some (mkAction 0 DL (Some 13))
  | 12, 4 => Some (mkAction 2 DL (Some 14))
  (* State N (13): 3RB --- 0LN 0LN --- *)
  | 13, 0 => Some (mkAction 3 DR (Some 1))
  | 13, 2 => Some (mkAction 0 DL (Some 13))
  | 13, 3 => Some (mkAction 0 DL (Some 13))
  (* State O (14): 0RC --- 2LO 2LO 2LD *)
  | 14, 0 => Some (mkAction 0 DR (Some 2))
  | 14, 2 => Some (mkAction 2 DL (Some 14))
  | 14, 3 => Some (mkAction 2 DL (Some 14))
  | 14, 4 => Some (mkAction 2 DL (Some 3))
  | _, _ => None
  end.

Lemma bb15_5_valid : ValidTM 15 5 bb15_5.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|sym]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|sym]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb15_5_core : Fwpw_5Core bb15_5 7 1 2 3 4 5 6 0 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb15_5_step_0 : StepF5Odd bb15_5 7 0 f_omega_omega.
Proof.
  apply (w5_stepFOdd_omega_omega bb15_5 7 1 2 3 4 5 6 0 8 9 10 11 0 bb15_5_core).
  apply (w5_base_rewrite bb15_5 7 1 2 3 4 5 6 0 8 9 10 11 0 bb15_5_core eq_refl eq_refl).
Qed.

Lemma bb15_5_rew_22 : forall n x R, 1 <= n ->
  exists t, Reaches bb15_5 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) t.
Proof.
  intros n x R Hn.
  assert (H1 : Reaches bb15_5 (H5cfg 7 n 1 (2 :: 2 :: x :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb15_5 7 2 1 (Some 12) _ (2 :: x :: R) eq_refl)).
  assert (H2 : Reaches bb15_5 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (2 :: x :: R)) (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  assert (H3 : Reaches bb15_5 (mkCfgR (Some 13) (2 :: rep n 3 []) (2 :: 0 :: x :: R)) (mkCfgR (Some 13) (rep n 3 []) (2 :: 0 :: 0 :: x :: R)) 1)
    by (apply steps_one; unfold step, mkCfgR; simpl; reflexivity).
  pose proof (w5_sweep_left_23_ne bb15_5 13 0 n 0 (0 :: x :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb15_5 (mkCfgR (Some 13) [] (0 :: rep (S n) 0 (0 :: 0 :: x :: R))) (mkCfgR (Some 1) [3] (rep (S n) 0 (0 :: 0 :: x :: R))) 1)
    by (apply (w8_step_R bb15_5 13 0 2 (Some 1) [] _ eq_refl)).
  assert (H6 : Reaches bb15_5 (mkCfgR (Some 1) [3] (0 :: rep n 0 (0 :: 0 :: x :: R))) (H5cfg 7 1 1 (rep (n + 2) 0 (x :: R))) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb15_5 1 0 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma bb15_5_pair_2 : StepF5Odd_pair_ne bb15_5 7 2 (f_omega_omega_plus 1).
Proof.
  exact (StepF5Odd_pair_ne_from_sym bb15_5 7 2 0 f_omega_omega f_omega_omega_props bb15_5_step_0 bb15_5_rew_22).
Qed.

Lemma bb15_5_rew_24 : forall n R, 1 <= n -> Nat.Odd n ->
  exists t, Reaches bb15_5 (H5cfg 7 n 1 (2 :: 4 :: R)) (H5cfg 7 1 1 (rep (n + 2) 2 R)) t.
Proof.
  intros n R Hn Ho.
  assert (H1 : Reaches bb15_5 (H5cfg 7 n 1 (2 :: 4 :: R)) (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) 1)
    by (unfold H5cfg; apply (w8_step_R bb15_5 7 2 1 (Some 12) _ (4 :: R) eq_refl)).
  assert (H2 : Reaches bb15_5 (mkCfgR (Some 12) (2 :: 2 :: rep n 3 []) (4 :: R)) (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  assert (H3 : Reaches bb15_5 (mkCfgR (Some 14) (2 :: rep n 3 []) (2 :: 2 :: R)) (mkCfgR (Some 14) (rep n 3 []) (2 :: 2 :: 2 :: R)) 1)
    by (apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb15_5 14 1 n (2 :: 2 :: R) eq_refl eq_refl) as H4.
  assert (H5 : Reaches bb15_5 (mkCfgR (Some 14) [] (0 :: rep (S n) 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb15_5 (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H7 : Reaches bb15_5 (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: 2 :: R))) (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H8 : Reaches bb15_5 (mkCfgR (Some 1) [3] (3 :: rep n 2 (2 :: 2 :: R))) (H5cfg 7 1 1 (rep (n + 2) 2 R)) 1).
  { unfold H5cfg. rewrite !rep_r8. replace (S (S n)) with (n + 2) by lia.
     apply (w8_step_R bb15_5 1 3 1 (Some 7) [3] _ eq_refl). }
  exists (1 + 1 + 1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] | exact H8].
Qed.

Lemma bb15_5_peeker_24 : StepF5Odd_peeker bb15_5 7 2 4 (f_omega_omega_plus 2).
Proof.
  exact (StepF5Odd_peeker_from_pair bb15_5 7 2 4 (f_omega_omega_plus 1)
           (fPlus_props _ f_omega_omega_props 1) (f_omega_omega_plus_ge_2n 1) bb15_5_pair_2 bb15_5_rew_24).
Qed.

Lemma bb15_5_init :
  Reaches bb15_5 initConfig (H5cfg 7 1 2 (1 :: 4 :: 0 :: 0 :: 2 :: rep 27 4 [])) 825.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB15_5_champion :
  ValidTM 15 5 bb15_5 /\
  exists t, HaltsIn bb15_5 initConfig t /\ f_omega_omega_plus 3 27 < t.
Proof.
  split; [exact bb15_5_valid |].
  pose proof bb15_5_init as H0.
  destruct (w5_init_14_odd bb15_5 7 1 2 3 4 5 6 0 8 9 10 11 bb15_5_core (0 :: 0 :: 2 :: rep 27 4 [])) as [n1 [t1 [H1 [Hn1 [_ Ho1]]]]].
  destruct (bb15_5_step_0 n1 (0 :: 2 :: rep 27 4 []) ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (bb15_5_step_0 n2 (2 :: rep 27 4 []) ltac:(lia) Ho2) as [n3 [t3 [H3 [Hinc3 [_ [_ Ho3]]]]]].
  destruct (StepF5Odd_peeker_rep bb15_5 7 2 4 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) bb15_5_peeker_24 27 n3 [] ltac:(lia) Ho3)
    as [n4 [t4 [H4 [Hinc4 [Hf4 [Ht4 _]]]]]].
  assert (Hhalt1 : Reaches bb15_5 (H5cfg 7 n4 1 [2]) (mkCfgR (Some 12) (2 :: 2 :: rep n4 3 []) []) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  assert (Hhalt2 : Reaches bb15_5 (mkCfgR (Some 12) (2 :: 2 :: rep n4 3 []) []) (mkCfgR None (1 :: 2 :: 2 :: rep n4 3 []) []) 1)
    by (apply steps_one; reflexivity).
  exists (825 + t1 + t2 + t3 + t4 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: 2 :: rep n4 3 []) []). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4] | exact Hhalt1] | exact Hhalt2].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf4 27 ltac:(lia) ltac:(lia)) as Hc.
    specialize (Ht4 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB15_5_champion.
