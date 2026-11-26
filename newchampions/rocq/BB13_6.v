(*
  rocq/BB13_6.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(13, 6):
    TM: 1LF3RA1LD2RB1RM---_1RZ3LA4LH2RB3LL2LM_3RA1LA3LC2RC------_2RE4RK3LC2RC---0LC_3RA2RE2RE4RF1RM---_1LG1RF3LG3RF4LG1LA_2RJ0LH2LG2LI4LK---_3LD1LH1LG3LH4LH---_2RC1LI3LG3LI4LI---_1RH1RJ2RJ3RJ4RF---_---1LK3LE3LK4RE---_3RA1LL1LL1LL------_0RC5LM2LM2LM4LF---
    Domain: BB(13, 6) (13 states, 6 symbols)
    Previous best dominated bound: BB(12, 6)
    Proved bound here: ValidTM 13 6 bb13_6 /\ exists t, HaltsIn bb13_6 initConfig t /\ f_omega_omega_plus 2 6 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_5_Ladder.
Import ListNotations.

Definition bb13_6 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1LF 3RA 1LD 2RB 1RM --- *)
  | 0, 0 => Some (mkAction 1 DL (Some 5))
  | 0, 1 => Some (mkAction 3 DR (Some 0))
  | 0, 2 => Some (mkAction 1 DL (Some 3))
  | 0, 3 => Some (mkAction 2 DR (Some 1))
  | 0, 4 => Some (mkAction 1 DR (Some 12))
  (* State B (1): 1RZ 3LA 4LH 2RB 3LL 2LM *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DL (Some 0))
  | 1, 2 => Some (mkAction 4 DL (Some 7))
  | 1, 3 => Some (mkAction 2 DR (Some 1))
  | 1, 4 => Some (mkAction 3 DL (Some 11))
  | 1, 5 => Some (mkAction 2 DL (Some 12))
  (* State C (2): 3RA 1LA 3LC 2RC --- --- *)
  | 2, 0 => Some (mkAction 3 DR (Some 0))
  | 2, 1 => Some (mkAction 1 DL (Some 0))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  (* State D (3): 2RE 4RK 3LC 2RC --- 0LC *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 1 => Some (mkAction 4 DR (Some 10))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 5 => Some (mkAction 0 DL (Some 2))
  (* State E (4): 3RA 2RE 2RE 4RF 1RM --- *)
  | 4, 0 => Some (mkAction 3 DR (Some 0))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 4 => Some (mkAction 1 DR (Some 12))
  (* State F (5): 1LG 1RF 3LG 3RF 4LG 1LA *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 6))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 6))
  | 5, 5 => Some (mkAction 1 DL (Some 0))
  (* State G (6): 2RJ 0LH 2LG 2LI 4LK --- *)
  | 6, 0 => Some (mkAction 2 DR (Some 9))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DL (Some 8))
  | 6, 4 => Some (mkAction 4 DL (Some 10))
  (* State H (7): 3LD 1LH 1LG 3LH 4LH --- *)
  | 7, 0 => Some (mkAction 3 DL (Some 3))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 6))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 4 DL (Some 7))
  (* State I (8): 2RC 1LI 3LG 3LI 4LI --- *)
  | 8, 0 => Some (mkAction 2 DR (Some 2))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 3 DL (Some 6))
  | 8, 3 => Some (mkAction 3 DL (Some 8))
  | 8, 4 => Some (mkAction 4 DL (Some 8))
  (* State J (9): 1RH 1RJ 2RJ 3RJ 4RF --- *)
  | 9, 0 => Some (mkAction 1 DR (Some 7))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): --- 1LK 3LE 3LK 4RE --- *)
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  | 10, 4 => Some (mkAction 4 DR (Some 4))
  (* State L (11): 3RA 1LL 1LL 1LL --- --- *)
  | 11, 0 => Some (mkAction 3 DR (Some 0))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* State M (12): 0RC 5LM 2LM 2LM 4LF --- *)
  | 12, 0 => Some (mkAction 0 DR (Some 2))
  | 12, 1 => Some (mkAction 5 DL (Some 12))
  | 12, 2 => Some (mkAction 2 DL (Some 12))
  | 12, 3 => Some (mkAction 2 DL (Some 12))
  | 12, 4 => Some (mkAction 4 DL (Some 5))
  | _, _ => None
  end.

Lemma bb13_6_valid : ValidTM 13 6 bb13_6.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|sym]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|sym]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb13_6_core : Fwpw_5Core bb13_6 1 0 2 3 4 5 6 7 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb13_6_init :
  Reaches bb13_6 initConfig (H5cfg 1 1 2 (1 :: 4 :: 2 :: rep 6 5 [])) 67.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb13_6_step_2 : StepF5 bb13_6 1 2 f_omega_omega.
Proof.
  apply (w5_stepF_omega_omega bb13_6 1 0 2 3 4 5 6 7 8 9 10 11 2 bb13_6_core).
  apply (w5_base_rewrite bb13_6 1 0 2 3 4 5 6 7 8 9 10 11 2 bb13_6_core eq_refl eq_refl).
Qed.

Lemma bb13_6_rew_5 : forall n R, 1 <= n ->
  exists t, Reaches bb13_6 (H5cfg 1 n 1 (5 :: R)) (H5cfg 1 1 1 (rep (S n) 2 R)) t.
Proof.
  intros n R Hn.
  assert (H1 : Reaches bb13_6 (H5cfg 1 n 1 (5 :: R)) (mkCfgR (Some 12) (rep n 3 []) (2 :: 2 :: R)) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  pose proof (w5_sweep_left_23 bb13_6 12 1 n (2 :: R) eq_refl eq_refl) as H2.
  assert (H3 : Reaches bb13_6 (mkCfgR (Some 12) [] (0 :: rep (S n) 2 (2 :: R))) (mkCfgR (Some 2) [] (rep (S n) 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H4 : Reaches bb13_6 (mkCfgR (Some 2) [] (2 :: rep n 2 (2 :: R))) (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H5 : Reaches bb13_6 (mkCfgR (Some 2) [] (0 :: 3 :: rep n 2 (2 :: R))) (mkCfgR (Some 0) [3] (3 :: rep n 2 (2 :: R))) 1)
    by (apply steps_one; reflexivity).
  assert (H6 : Reaches bb13_6 (mkCfgR (Some 0) [3] (3 :: rep n 2 (2 :: R))) (H5cfg 1 1 1 (rep (S n) 2 R)) 1)
    by (unfold H5cfg; rewrite rep_r8; apply (w8_step_R bb13_6 0 3 1 (Some 1) [3] (rep (S n) 2 R) eq_refl)).
  exists (1 + S n + 1 + 1 + 1 + 1).
  eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
Qed.

Lemma bb13_6_step_5 : StepF5 bb13_6 1 5 (f_omega_omega_plus 1).
Proof.
  exact (StepF5_next bb13_6 1 5 2 f_omega_omega f_omega_omega_props bb13_6_step_2 bb13_6_rew_5).
Qed.

Theorem BB13_6_champion :
  ValidTM 13 6 bb13_6 /\
  exists t, HaltsIn bb13_6 initConfig t /\ f_omega_omega_plus 2 6 < t.
Proof.
  split; [exact bb13_6_valid |].
  pose proof bb13_6_init as H0.
  destruct (w5_init_14_odd bb13_6 1 0 2 3 4 5 6 7 8 9 10 11 bb13_6_core (2 :: rep 6 5 [])) as [n1 [t1 [H1 [Hn1 [_ _]]]]].
  destruct (bb13_6_step_2 n1 (rep 6 5 []) ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [_ _]]]]].
  destruct (StepF5_rep bb13_6 1 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) bb13_6_step_5 6 n2 [] ltac:(lia)) as [n3 [t3 [H3 [Hinc3 [Hf3 Ht3]]]]].
  assert (Hhalt : Reaches bb13_6 (H5cfg 1 n3 1 []) (mkCfgR None (1 :: 2 :: rep n3 3 []) []) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  exists (67 + t1 + t2 + t3 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n3 3 []) []). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf3 6 ltac:(lia) ltac:(lia)) as Hc.
    specialize (Ht3 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB13_6_champion.
