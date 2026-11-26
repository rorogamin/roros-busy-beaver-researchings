(*
  rocq/BB14_7.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(14, 7):
    TM: 0LK3RA1LD2RB------4RC_1RZ3LA4LH2RB3LL2LM5LN_3RA1LA3LC2RC---0LH---_2RE---3LC2RC---2LK---_3RA2RE2RE4RF---1LJ5RD_1LG1RF3LG3RF4LG6LF6LN_2RJ0LH2LG2LI4LK------_---1LH1LG3LH4LH------_2RC1LI3LG3LI4LI------_6LA1RJ2RJ3RJ4RF------_0LG1LK3LE3LK---6LE---_3RA1LL1LL1LL---------_0RC---2LM2LM---------_3RN5RD5LN5LN6LK2RB---
    Domain: BB(14, 7) (14 states, 7 symbols)
    Previous best dominated bound: BB(12, 6)
    Proved bound here: ValidTM 14 7 bb14_7 /\ exists t, HaltsIn bb14_7 initConfig t /\ f_omega_omega_plus 3 22 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_5_Ladder.
Import ListNotations.

Definition bb14_7 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 0LK 3RA 1LD 2RB --- --- 4RC *)
  | 0, 0 => Some (mkAction 0 DL (Some 10))
  | 0, 1 => Some (mkAction 3 DR (Some 0))
  | 0, 2 => Some (mkAction 1 DL (Some 3))
  | 0, 3 => Some (mkAction 2 DR (Some 1))
  | 0, 6 => Some (mkAction 4 DR (Some 2))
  (* State B (1): 1RZ 3LA 4LH 2RB 3LL 2LM 5LN *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DL (Some 0))
  | 1, 2 => Some (mkAction 4 DL (Some 7))
  | 1, 3 => Some (mkAction 2 DR (Some 1))
  | 1, 4 => Some (mkAction 3 DL (Some 11))
  | 1, 5 => Some (mkAction 2 DL (Some 12))
  | 1, 6 => Some (mkAction 5 DL (Some 13))
  (* State C (2): 3RA 1LA 3LC 2RC --- 0LH --- *)
  | 2, 0 => Some (mkAction 3 DR (Some 0))
  | 2, 1 => Some (mkAction 1 DL (Some 0))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 5 => Some (mkAction 0 DL (Some 7))
  (* State D (3): 2RE --- 3LC 2RC --- 2LK --- *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 5 => Some (mkAction 2 DL (Some 10))
  (* State E (4): 3RA 2RE 2RE 4RF --- 1LJ 5RD *)
  | 4, 0 => Some (mkAction 3 DR (Some 0))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 5 => Some (mkAction 1 DL (Some 9))
  | 4, 6 => Some (mkAction 5 DR (Some 3))
  (* State F (5): 1LG 1RF 3LG 3RF 4LG 6LF 6LN *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 6))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 6))
  | 5, 5 => Some (mkAction 6 DL (Some 5))
  | 5, 6 => Some (mkAction 6 DL (Some 13))
  (* State G (6): 2RJ 0LH 2LG 2LI 4LK --- --- *)
  | 6, 0 => Some (mkAction 2 DR (Some 9))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DL (Some 8))
  | 6, 4 => Some (mkAction 4 DL (Some 10))
  (* State H (7): --- 1LH 1LG 3LH 4LH --- --- *)
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 6))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 4 DL (Some 7))
  (* State I (8): 2RC 1LI 3LG 3LI 4LI --- --- *)
  | 8, 0 => Some (mkAction 2 DR (Some 2))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 3 DL (Some 6))
  | 8, 3 => Some (mkAction 3 DL (Some 8))
  | 8, 4 => Some (mkAction 4 DL (Some 8))
  (* State J (9): 6LA 1RJ 2RJ 3RJ 4RF --- --- *)
  | 9, 0 => Some (mkAction 6 DL (Some 0))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): 0LG 1LK 3LE 3LK --- 6LE --- *)
  | 10, 0 => Some (mkAction 0 DL (Some 6))
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  | 10, 5 => Some (mkAction 6 DL (Some 4))
  (* State L (11): 3RA 1LL 1LL 1LL --- --- --- *)
  | 11, 0 => Some (mkAction 3 DR (Some 0))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* State M (12): 0RC --- 2LM 2LM --- --- --- *)
  | 12, 0 => Some (mkAction 0 DR (Some 2))
  | 12, 2 => Some (mkAction 2 DL (Some 12))
  | 12, 3 => Some (mkAction 2 DL (Some 12))
  (* State N (13): 3RN 5RD 5LN 5LN 6LK 2RB --- *)
  | 13, 0 => Some (mkAction 3 DR (Some 13))
  | 13, 1 => Some (mkAction 5 DR (Some 3))
  | 13, 2 => Some (mkAction 5 DL (Some 13))
  | 13, 3 => Some (mkAction 5 DL (Some 13))
  | 13, 4 => Some (mkAction 6 DL (Some 10))
  | 13, 5 => Some (mkAction 2 DR (Some 1))
  | _, _ => None
  end.

Lemma bb14_7_valid : ValidTM 14 7 bb14_7.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|sym]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|sym]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb14_7_core : Fwpw_5Core bb14_7 1 0 2 3 4 5 6 7 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb14_7_init :
  Reaches bb14_7 initConfig (H5cfg 1 1 2 (1 :: 4 :: 2 :: 5 :: rep 22 6 [])) 629.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb14_7_step_2 : StepF5 bb14_7 1 2 f_omega_omega.
Proof.
  apply (w5_stepF_omega_omega bb14_7 1 0 2 3 4 5 6 7 8 9 10 11 2 bb14_7_core).
  apply (w5_base_rewrite bb14_7 1 0 2 3 4 5 6 7 8 9 10 11 2 bb14_7_core eq_refl eq_refl).
Qed.

Lemma bb14_7_rew_5 : forall n R, 1 <= n ->
  exists t, Reaches bb14_7 (H5cfg 1 n 1 (5 :: R)) (H5cfg 1 1 1 (rep (S n) 2 R)) t.
Proof.
  intros n R Hn.
  assert (H1 : Reaches bb14_7 (H5cfg 1 n 1 (5 :: R)) (mkCfgR (Some 12) (rep n 3 []) (2 :: 2 :: R)) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb14_7 12 1 n (2 :: R) eq_refl eq_refl) as H2.
  assert (H3 : Reaches bb14_7 (mkCfgR (Some 12) [] (0 :: rep (S n) 2 (2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H4 : Reaches bb14_7 (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H5 : Reaches bb14_7 (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) (mkCfgR (Some 0) [3] (3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb14_7 (mkCfgR (Some 0) [3] (3 :: rep n 2 (2 :: R))) (H5cfg 1 1 1 (rep (S n) 2 R)) 1)
    by (unfold H5cfg; rewrite rep_r8; apply (w8_step_R bb14_7 0 3 1 (Some 1) [3] (rep (S n) 2 R) eq_refl)).
  exists (1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma bb14_7_step_5 : StepF5 bb14_7 1 5 (f_omega_omega_plus 1).
Proof.
  exact (StepF5_next bb14_7 1 5 2 f_omega_omega f_omega_omega_props bb14_7_step_2 bb14_7_rew_5).
Qed.

Lemma bb14_7_rew_6 : forall n R, 1 <= n ->
  exists t, Reaches bb14_7 (H5cfg 1 n 1 (6 :: R)) (H5cfg 1 1 1 (rep (S n) 5 R)) t.
Proof.
  intros n R Hn.
  assert (H1 : Reaches bb14_7 (H5cfg 1 n 1 (6 :: R)) (mkCfgR (Some 13) (rep n 3 []) (2 :: 5 :: R)) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb14_7 13 4 n (5 :: R) eq_refl eq_refl) as H2.
  assert (H3 : Reaches bb14_7 (mkCfgR (Some 13) [] (0 :: rep (S n) 5 (5 :: R))) (mkCfgR (Some 13) [3] (rep (S n) 5 (5 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H4 : Reaches bb14_7 (mkCfgR (Some 13) [3] (5 :: rep n 5 (5 :: R))) (H5cfg 1 1 1 (rep (S n) 5 R)) 1)
    by (unfold H5cfg; rewrite rep_r8; apply (w8_step_R bb14_7 13 5 1 (Some 1) [3] (rep (S n) 5 R) eq_refl)).
  exists (1 + S n + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4].
Qed.

Lemma bb14_7_step_6 : StepF5 bb14_7 1 6 (f_omega_omega_plus 2).
Proof.
  exact (StepF5_next bb14_7 1 6 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) bb14_7_step_5 bb14_7_rew_6).
Qed.

Theorem BB14_7_champion :
  ValidTM 14 7 bb14_7 /\
  exists t, HaltsIn bb14_7 initConfig t /\ f_omega_omega_plus 3 22 < t.
Proof.
  split; [exact bb14_7_valid |].
  pose proof bb14_7_init as H0.
  destruct (w5_init_14_odd bb14_7 1 0 2 3 4 5 6 7 8 9 10 11 bb14_7_core (2 :: 5 :: rep 22 6 [])) as [n1 [t1 [H1 [Hn1 [_ _]]]]].
  destruct (bb14_7_step_2 n1 (5 :: rep 22 6 []) ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [_ _]]]]].
  destruct (bb14_7_step_5 n2 (rep 22 6 []) ltac:(lia)) as [n3 [t3 [H3 [Hinc3 [_ _]]]]].
  destruct (StepF5_rep bb14_7 1 6 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) bb14_7_step_6 22 n3 [] ltac:(lia)) as [n4 [t4 [H4 [Hinc4 [Hf4 Ht4]]]]].
  assert (Hhalt : Reaches bb14_7 (H5cfg 1 n4 1 []) (mkCfgR None (1 :: 2 :: rep n4 3 []) []) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  exists (629 + t1 + t2 + t3 + t4 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n4 3 []) []). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf4 22 ltac:(lia) ltac:(lia)) as Hc.
    specialize (Ht4 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB14_7_champion.
