(*
  rocq/BB13_5.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(13, 5):
    TM: 4LH3LB1RZ2RA3LL_3LH3RB1LD2RA3LB_3RB1LB3LC2RC4RC_2RE2LL3LC2RC4LB_3RB2RE2RE4RF0RH_1LG1RF3LG3RF4LG_2RJ0LH2LG2LI4LK_4RJ1LH1LG3LH4LH_2RC1LI3LG3LI4LI_2LB1RJ2RJ3RJ4RF_---1LK3LE3LK1RF_3RB1LL1LL1LL0LM_3LL---0LM------
    Domain: BB(13, 5) (13 states, 5 symbols)
    Previous best dominated bound: BB(12, 5)
    Proved bound here: ValidTM 13 5 bb13_5 /\ exists t, HaltsIn bb13_5 initConfig t /\ f_omega_omega_plus 1 9 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_5 Fwpw_5_Ladder.
Import ListNotations.

Definition bb13_5 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 4LH 3LB 1RZ 2RA 3LL *)
  | 0, 0 => Some (mkAction 4 DL (Some 7))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 1 DR None)
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 3 DL (Some 11))
  (* State B (1): 3LH 3RB 1LD 2RA 3LB *)
  | 1, 0 => Some (mkAction 3 DL (Some 7))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 1))
  (* State C (2): 3RB 1LB 3LC 2RC 4RC *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DR (Some 2))
  (* State D (3): 2RE 2LL 3LC 2RC 4LB *)
  | 3, 0 => Some (mkAction 2 DR (Some 4))
  | 3, 1 => Some (mkAction 2 DL (Some 11))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 4 DL (Some 1))
  (* State E (4): 3RB 2RE 2RE 4RF 0RH *)
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 2 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 4))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 4 => Some (mkAction 0 DR (Some 7))
  (* State F (5): 1LG 1RF 3LG 3RF 4LG *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 6))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 6))
  (* State G (6): 2RJ 0LH 2LG 2LI 4LK *)
  | 6, 0 => Some (mkAction 2 DR (Some 9))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DL (Some 8))
  | 6, 4 => Some (mkAction 4 DL (Some 10))
  (* State H (7): 4RJ 1LH 1LG 3LH 4LH *)
  | 7, 0 => Some (mkAction 4 DR (Some 9))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 6))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 4 DL (Some 7))
  (* State I (8): 2RC 1LI 3LG 3LI 4LI *)
  | 8, 0 => Some (mkAction 2 DR (Some 2))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 3 DL (Some 6))
  | 8, 3 => Some (mkAction 3 DL (Some 8))
  | 8, 4 => Some (mkAction 4 DL (Some 8))
  (* State J (9): 2LB 1RJ 2RJ 3RJ 4RF *)
  | 9, 0 => Some (mkAction 2 DL (Some 1))
  | 9, 1 => Some (mkAction 1 DR (Some 9))
  | 9, 2 => Some (mkAction 2 DR (Some 9))
  | 9, 3 => Some (mkAction 3 DR (Some 9))
  | 9, 4 => Some (mkAction 4 DR (Some 5))
  (* State K (10): --- 1LK 3LE 3LK 1RF *)
  | 10, 1 => Some (mkAction 1 DL (Some 10))
  | 10, 2 => Some (mkAction 3 DL (Some 4))
  | 10, 3 => Some (mkAction 3 DL (Some 10))
  | 10, 4 => Some (mkAction 1 DR (Some 5))
  (* State L (11): 3RB 1LL 1LL 1LL 0LM *)
  | 11, 0 => Some (mkAction 3 DR (Some 1))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  | 11, 4 => Some (mkAction 0 DL (Some 12))
  (* State M (12): 3LL --- 0LM --- --- *)
  | 12, 0 => Some (mkAction 3 DL (Some 11))
  | 12, 2 => Some (mkAction 0 DL (Some 12))
  | _, _ => None
  end.

Lemma bb13_5_valid : ValidTM 13 5 bb13_5.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|sym]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|sym]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb13_5_core : Fwpw_5Core bb13_5 0 1 2 3 4 5 6 7 8 9 10 11.
Proof. constructor; reflexivity. Qed.

Lemma bb13_5_init :
  Reaches bb13_5 initConfig (H5cfg 0 1 2 (1 :: 4 :: rep 9 0 [2; 1; 1])) 148.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb13_5_step_0 : StepF5 bb13_5 0 0 f_omega_omega.
Proof.
  apply (w5_stepF_omega_omega bb13_5 0 1 2 3 4 5 6 7 8 9 10 11 0 bb13_5_core).
  apply (w5_base_rewrite bb13_5 0 1 2 3 4 5 6 7 8 9 10 11 0 bb13_5_core eq_refl eq_refl).
Qed.

Theorem BB13_5_champion :
  ValidTM 13 5 bb13_5 /\
  exists t, HaltsIn bb13_5 initConfig t /\ f_omega_omega_plus 1 9 < t.
Proof.
  split; [exact bb13_5_valid |].
  pose proof bb13_5_init as H0.
  destruct (w5_init_14_odd bb13_5 0 1 2 3 4 5 6 7 8 9 10 11 bb13_5_core (rep 9 0 [2; 1; 1])) as [n1 [t1 [H1 [Hn1 [_ _]]]]].
  destruct (StepF5_rep bb13_5 0 0 f_omega_omega f_omega_omega_props bb13_5_step_0 9 n1 [2; 1; 1] ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [Hf2 Ht2]]]]].
  assert (Hhalt : Reaches bb13_5 (H5cfg 0 n2 1 [2; 1; 1]) (mkCfgR None (1 :: 2 :: rep n2 3 []) [1; 1]) 1)
    by (unfold H5cfg; apply steps_one; reflexivity).
  exists (148 + t1 + t2 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n2 3 []) [1; 1]). split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf2 9 ltac:(lia) ltac:(lia)) as H9.
    specialize (Ht2 ltac:(lia)).
    rewrite (HfPlus_S 0 9). change (f_omega_omega_plus 0) with f_omega_omega. lia.
Qed.

Print Assumptions BB13_5_champion.
