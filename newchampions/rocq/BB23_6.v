(*
  rocq/BB23_6.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(23, 6):
    TM: 1LE1LN0RK0RM4LN0RQ_1RZ1RB2LI1RV1RB5LI_0LI5RC2RC3RC2RC5RC_1LE1RD2RD3RD3LW5RD_3LO1LE2LE3LE4RS5LE_0LG1RF2RF3RF1LR5RF_0RI0LH---3RI4RI0LW_2LO1LH2LH3LH5LO5LH_3RP4RC0LO0LI0LD2LS_2RA0RF2LJ3LJ0RF5LJ_2LU1RK2RK3RK4RK5RK_3RA1LL2LL3LL4LL5LL_3LL1RM2RM3RM4RM5RM_1RB1LN2LN3LN1LO5LN_1RB4RP0RF0RD1LN4RF_4LJ1RP2RP3RP0RP5RP_5LR1RQ2RQ3RQ4RQ5RQ_5RA1LR2LR3LR4LR5LR_1RB4RT2LS3LS4LS5LS_2LS5LF2RT3RT4RT5RT_2RA1LU2LU3LU4LU5LU_3RH4RE4LW---5LW4RS_4RD5RV---------0RD
    Core: fe1_6 @ step 423: 1^9 B> 5^13 0^inf
    Proved bound: ValidTM 23 6 bb23_6 /\ exists t, HaltsIn bb23_6 initConfig t /\ f_epsilon1 10 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fe1.
Import ListNotations.

Definition bb23_6 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1LE 1LN 0RK 0RM 4LN 0RQ *)
  | 0, 0 => Some (mkAction 1 DL (Some 4))
  | 0, 1 => Some (mkAction 1 DL (Some 13))
  | 0, 2 => Some (mkAction 0 DR (Some 10))
  | 0, 3 => Some (mkAction 0 DR (Some 12))
  | 0, 4 => Some (mkAction 4 DL (Some 13))
  | 0, 5 => Some (mkAction 0 DR (Some 16))
  (* State B (1): 1RZ 1RB 2LI 1RV 1RB 5LI *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 1 DR (Some 1))
  | 1, 2 => Some (mkAction 2 DL (Some 8))
  | 1, 3 => Some (mkAction 1 DR (Some 21))
  | 1, 4 => Some (mkAction 1 DR (Some 1))
  | 1, 5 => Some (mkAction 5 DL (Some 8))
  (* State C (2): 0LI 5RC 2RC 3RC 2RC 5RC *)
  | 2, 0 => Some (mkAction 0 DL (Some 8))
  | 2, 1 => Some (mkAction 5 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 2))
  | 2, 3 => Some (mkAction 3 DR (Some 2))
  | 2, 4 => Some (mkAction 2 DR (Some 2))
  | 2, 5 => Some (mkAction 5 DR (Some 2))
  (* State D (3): 1LE 1RD 2RD 3RD 3LW 5RD *)
  | 3, 0 => Some (mkAction 1 DL (Some 4))
  | 3, 1 => Some (mkAction 1 DR (Some 3))
  | 3, 2 => Some (mkAction 2 DR (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  | 3, 4 => Some (mkAction 3 DL (Some 22))
  | 3, 5 => Some (mkAction 5 DR (Some 3))
  (* State E (4): 3LO 1LE 2LE 3LE 4RS 5LE *)
  | 4, 0 => Some (mkAction 3 DL (Some 14))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 2 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  | 4, 4 => Some (mkAction 4 DR (Some 18))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  (* State F (5): 0LG 1RF 2RF 3RF 1LR 5RF *)
  | 5, 0 => Some (mkAction 0 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 2 DR (Some 5))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 1 DL (Some 17))
  | 5, 5 => Some (mkAction 5 DR (Some 5))
  (* State G (6): 0RI 0LH --- 3RI 4RI 0LW *)
  | 6, 0 => Some (mkAction 0 DR (Some 8))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 3 => Some (mkAction 3 DR (Some 8))
  | 6, 4 => Some (mkAction 4 DR (Some 8))
  | 6, 5 => Some (mkAction 0 DL (Some 22))
  (* State H (7): 2LO 1LH 2LH 3LH 5LO 5LH *)
  | 7, 0 => Some (mkAction 2 DL (Some 14))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 2 DL (Some 7))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 5 DL (Some 14))
  | 7, 5 => Some (mkAction 5 DL (Some 7))
  (* State I (8): 3RP 4RC 0LO 0LI 0LD 2LS *)
  | 8, 0 => Some (mkAction 3 DR (Some 15))
  | 8, 1 => Some (mkAction 4 DR (Some 2))
  | 8, 2 => Some (mkAction 0 DL (Some 14))
  | 8, 3 => Some (mkAction 0 DL (Some 8))
  | 8, 4 => Some (mkAction 0 DL (Some 3))
  | 8, 5 => Some (mkAction 2 DL (Some 18))
  (* State J (9): 2RA 0RF 2LJ 3LJ 0RF 5LJ *)
  | 9, 0 => Some (mkAction 2 DR (Some 0))
  | 9, 1 => Some (mkAction 0 DR (Some 5))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | 9, 4 => Some (mkAction 0 DR (Some 5))
  | 9, 5 => Some (mkAction 5 DL (Some 9))
  (* State K (10): 2LU 1RK 2RK 3RK 4RK 5RK *)
  | 10, 0 => Some (mkAction 2 DL (Some 20))
  | 10, 1 => Some (mkAction 1 DR (Some 10))
  | 10, 2 => Some (mkAction 2 DR (Some 10))
  | 10, 3 => Some (mkAction 3 DR (Some 10))
  | 10, 4 => Some (mkAction 4 DR (Some 10))
  | 10, 5 => Some (mkAction 5 DR (Some 10))
  (* State L (11): 3RA 1LL 2LL 3LL 4LL 5LL *)
  | 11, 0 => Some (mkAction 3 DR (Some 0))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 2 DL (Some 11))
  | 11, 3 => Some (mkAction 3 DL (Some 11))
  | 11, 4 => Some (mkAction 4 DL (Some 11))
  | 11, 5 => Some (mkAction 5 DL (Some 11))
  (* State M (12): 3LL 1RM 2RM 3RM 4RM 5RM *)
  | 12, 0 => Some (mkAction 3 DL (Some 11))
  | 12, 1 => Some (mkAction 1 DR (Some 12))
  | 12, 2 => Some (mkAction 2 DR (Some 12))
  | 12, 3 => Some (mkAction 3 DR (Some 12))
  | 12, 4 => Some (mkAction 4 DR (Some 12))
  | 12, 5 => Some (mkAction 5 DR (Some 12))
  (* State N (13): 1RB 1LN 2LN 3LN 1LO 5LN *)
  | 13, 0 => Some (mkAction 1 DR (Some 1))
  | 13, 1 => Some (mkAction 1 DL (Some 13))
  | 13, 2 => Some (mkAction 2 DL (Some 13))
  | 13, 3 => Some (mkAction 3 DL (Some 13))
  | 13, 4 => Some (mkAction 1 DL (Some 14))
  | 13, 5 => Some (mkAction 5 DL (Some 13))
  (* State O (14): 1RB 4RP 0RF 0RD 1LN 4RF *)
  | 14, 0 => Some (mkAction 1 DR (Some 1))
  | 14, 1 => Some (mkAction 4 DR (Some 15))
  | 14, 2 => Some (mkAction 0 DR (Some 5))
  | 14, 3 => Some (mkAction 0 DR (Some 3))
  | 14, 4 => Some (mkAction 1 DL (Some 13))
  | 14, 5 => Some (mkAction 4 DR (Some 5))
  (* State P (15): 4LJ 1RP 2RP 3RP 0RP 5RP *)
  | 15, 0 => Some (mkAction 4 DL (Some 9))
  | 15, 1 => Some (mkAction 1 DR (Some 15))
  | 15, 2 => Some (mkAction 2 DR (Some 15))
  | 15, 3 => Some (mkAction 3 DR (Some 15))
  | 15, 4 => Some (mkAction 0 DR (Some 15))
  | 15, 5 => Some (mkAction 5 DR (Some 15))
  (* State Q (16): 5LR 1RQ 2RQ 3RQ 4RQ 5RQ *)
  | 16, 0 => Some (mkAction 5 DL (Some 17))
  | 16, 1 => Some (mkAction 1 DR (Some 16))
  | 16, 2 => Some (mkAction 2 DR (Some 16))
  | 16, 3 => Some (mkAction 3 DR (Some 16))
  | 16, 4 => Some (mkAction 4 DR (Some 16))
  | 16, 5 => Some (mkAction 5 DR (Some 16))
  (* State R (17): 5RA 1LR 2LR 3LR 4LR 5LR *)
  | 17, 0 => Some (mkAction 5 DR (Some 0))
  | 17, 1 => Some (mkAction 1 DL (Some 17))
  | 17, 2 => Some (mkAction 2 DL (Some 17))
  | 17, 3 => Some (mkAction 3 DL (Some 17))
  | 17, 4 => Some (mkAction 4 DL (Some 17))
  | 17, 5 => Some (mkAction 5 DL (Some 17))
  (* State S (18): 1RB 4RT 2LS 3LS 4LS 5LS *)
  | 18, 0 => Some (mkAction 1 DR (Some 1))
  | 18, 1 => Some (mkAction 4 DR (Some 19))
  | 18, 2 => Some (mkAction 2 DL (Some 18))
  | 18, 3 => Some (mkAction 3 DL (Some 18))
  | 18, 4 => Some (mkAction 4 DL (Some 18))
  | 18, 5 => Some (mkAction 5 DL (Some 18))
  (* State T (19): 2LS 5LF 2RT 3RT 4RT 5RT *)
  | 19, 0 => Some (mkAction 2 DL (Some 18))
  | 19, 1 => Some (mkAction 5 DL (Some 5))
  | 19, 2 => Some (mkAction 2 DR (Some 19))
  | 19, 3 => Some (mkAction 3 DR (Some 19))
  | 19, 4 => Some (mkAction 4 DR (Some 19))
  | 19, 5 => Some (mkAction 5 DR (Some 19))
  (* State U (20): 2RA 1LU 2LU 3LU 4LU 5LU *)
  | 20, 0 => Some (mkAction 2 DR (Some 0))
  | 20, 1 => Some (mkAction 1 DL (Some 20))
  | 20, 2 => Some (mkAction 2 DL (Some 20))
  | 20, 3 => Some (mkAction 3 DL (Some 20))
  | 20, 4 => Some (mkAction 4 DL (Some 20))
  | 20, 5 => Some (mkAction 5 DL (Some 20))
  (* State V (21): 3RH 4RE 4LW --- 5LW 4RS *)
  | 21, 0 => Some (mkAction 3 DR (Some 7))
  | 21, 1 => Some (mkAction 4 DR (Some 4))
  | 21, 2 => Some (mkAction 4 DL (Some 22))
  | 21, 4 => Some (mkAction 5 DL (Some 22))
  | 21, 5 => Some (mkAction 4 DR (Some 18))
  (* State W (22): 4RD 5RV --- --- --- 0RD *)
  | 22, 0 => Some (mkAction 4 DR (Some 3))
  | 22, 1 => Some (mkAction 5 DR (Some 21))
  | 22, 5 => Some (mkAction 0 DR (Some 3))
  | _, _ => None
  end.

Lemma bb23_6_valid : ValidTM 23 6 bb23_6.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 23 (destruct s as [| s]; [ do 6 (destruct sym as [| sym]; [ simpl; try exact I; lia |]); lia |]); lia.
  - do 23 (destruct s as [| s]; [ do 6 (destruct sym as [| sym]; [ try lia; reflexivity |]); reflexivity |]); reflexivity.
Qed.

Lemma bb23_6_core : Fe1_6Core bb23_6.
Proof.
  constructor; try reflexivity; try discriminate; intros _; try reflexivity; lia.
Qed.

Lemma bb23_6_boot :
  Reaches bb23_6 initConfig (mkCfgR (Some 1) (rep 9 1 []) (rep 13 5 [])) 423.
Proof.
  unfold Reaches; vm_compute; reflexivity.
Qed.

Theorem BB23_6_champion :
  ValidTM 23 6 bb23_6 /\
  exists t, HaltsIn bb23_6 initConfig t /\ f_epsilon1 10 < t.
Proof.
  split; [exact bb23_6_valid |].
  destruct (Fe1_6_halts bb23_6 9 13 bb23_6_core ltac:(lia) ltac:(lia))
    as [t_core [[cf [Hsteps Hst]] Hbound]].
  exists (423 + t_core). split.
  - exists cf; split; [eapply steps_add; [exact bb23_6_boot | exact Hsteps] | exact Hst].
  - simpl in Hbound; lia.
Qed.

Print Assumptions BB23_6_champion.
