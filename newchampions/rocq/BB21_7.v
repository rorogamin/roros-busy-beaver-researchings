(*
  rocq/BB21_7.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(21, 7):
    TM: 6LF---0RF0RD1LN6RF---_1RZ1RB2LC4RF1RB5LC3LP_0LI4RC2RC3RC2RC5RC5RC_1LE1RD2RD3RD---5RD---_3LA1LE2LE3LE5LU5LE---_0LG1RF2RF3RF6LJ5RF5LH_0RI0LH---3RI------6RI_2LA1LH2LH3LH6LM5LH5LA_3RP---0LA0LI---2LS---_2RO5RO2LJ3LJ---5LJ1RF_2LL---2RK3RK4RK5RK6RK_3RO2RO2LL3LL4LL5LL6LL_3LL6LO2RM3RM4RM5RM6RM_1RB1LN2LN3LN1LO5LN4RE_1RB4RP1RK0RM4LN0RQ6LN_4LJ1RP2RP3RP0RP5RP6RP_5LR---2RQ3RQ4RQ5RQ6RQ_5RO---2LR3LR4LR5LR6LR_1RB4RT2LS3LS4LS5LS---_2LS---2RT3RT4RT5RT---_---------4RA6RH------
    Core: fe1_7 @ step 395: 1^2 B> 5^24 0^inf
    Proved bound: ValidTM 21 7 bb21_7 /\ exists t, HaltsIn bb21_7 initConfig t /\ f_epsilon1 21 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fe1.
Import ListNotations.

Definition bb21_7 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6LF --- 0RF 0RD 1LN 6RF --- *)
  | 0, 0 => Some (mkAction 6 DL (Some 5))
  | 0, 2 => Some (mkAction 0 DR (Some 5))
  | 0, 3 => Some (mkAction 0 DR (Some 3))
  | 0, 4 => Some (mkAction 1 DL (Some 13))
  | 0, 5 => Some (mkAction 6 DR (Some 5))
  (* State B (1): 1RZ 1RB 2LC 4RF 1RB 5LC 3LP *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 1 DR (Some 1))
  | 1, 2 => Some (mkAction 2 DL (Some 2))
  | 1, 3 => Some (mkAction 4 DR (Some 5))
  | 1, 4 => Some (mkAction 1 DR (Some 1))
  | 1, 5 => Some (mkAction 5 DL (Some 2))
  | 1, 6 => Some (mkAction 3 DL (Some 15))
  (* State C (2): 0LI 4RC 2RC 3RC 2RC 5RC 5RC *)
  | 2, 0 => Some (mkAction 0 DL (Some 8))
  | 2, 1 => Some (mkAction 4 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 2))
  | 2, 3 => Some (mkAction 3 DR (Some 2))
  | 2, 4 => Some (mkAction 2 DR (Some 2))
  | 2, 5 => Some (mkAction 5 DR (Some 2))
  | 2, 6 => Some (mkAction 5 DR (Some 2))
  (* State D (3): 1LE 1RD 2RD 3RD --- 5RD --- *)
  | 3, 0 => Some (mkAction 1 DL (Some 4))
  | 3, 1 => Some (mkAction 1 DR (Some 3))
  | 3, 2 => Some (mkAction 2 DR (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  | 3, 5 => Some (mkAction 5 DR (Some 3))
  (* State E (4): 3LA 1LE 2LE 3LE 5LU 5LE --- *)
  | 4, 0 => Some (mkAction 3 DL (Some 0))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 2 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  | 4, 4 => Some (mkAction 5 DL (Some 20))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  (* State F (5): 0LG 1RF 2RF 3RF 6LJ 5RF 5LH *)
  | 5, 0 => Some (mkAction 0 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 2 DR (Some 5))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 6 DL (Some 9))
  | 5, 5 => Some (mkAction 5 DR (Some 5))
  | 5, 6 => Some (mkAction 5 DL (Some 7))
  (* State G (6): 0RI 0LH --- 3RI --- --- 6RI *)
  | 6, 0 => Some (mkAction 0 DR (Some 8))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 3 => Some (mkAction 3 DR (Some 8))
  | 6, 6 => Some (mkAction 6 DR (Some 8))
  (* State H (7): 2LA 1LH 2LH 3LH 6LM 5LH 5LA *)
  | 7, 0 => Some (mkAction 2 DL (Some 0))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 2 DL (Some 7))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 6 DL (Some 12))
  | 7, 5 => Some (mkAction 5 DL (Some 7))
  | 7, 6 => Some (mkAction 5 DL (Some 0))
  (* State I (8): 3RP --- 0LA 0LI --- 2LS --- *)
  | 8, 0 => Some (mkAction 3 DR (Some 15))
  | 8, 2 => Some (mkAction 0 DL (Some 0))
  | 8, 3 => Some (mkAction 0 DL (Some 8))
  | 8, 5 => Some (mkAction 2 DL (Some 18))
  (* State J (9): 2RO 5RO 2LJ 3LJ --- 5LJ 1RF *)
  | 9, 0 => Some (mkAction 2 DR (Some 14))
  | 9, 1 => Some (mkAction 5 DR (Some 14))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DL (Some 9))
  | 9, 6 => Some (mkAction 1 DR (Some 5))
  (* State K (10): 2LL --- 2RK 3RK 4RK 5RK 6RK *)
  | 10, 0 => Some (mkAction 2 DL (Some 11))
  | 10, 2 => Some (mkAction 2 DR (Some 10))
  | 10, 3 => Some (mkAction 3 DR (Some 10))
  | 10, 4 => Some (mkAction 4 DR (Some 10))
  | 10, 5 => Some (mkAction 5 DR (Some 10))
  | 10, 6 => Some (mkAction 6 DR (Some 10))
  (* State L (11): 3RO 2RO 2LL 3LL 4LL 5LL 6LL *)
  | 11, 0 => Some (mkAction 3 DR (Some 14))
  | 11, 1 => Some (mkAction 2 DR (Some 14))
  | 11, 2 => Some (mkAction 2 DL (Some 11))
  | 11, 3 => Some (mkAction 3 DL (Some 11))
  | 11, 4 => Some (mkAction 4 DL (Some 11))
  | 11, 5 => Some (mkAction 5 DL (Some 11))
  | 11, 6 => Some (mkAction 6 DL (Some 11))
  (* State M (12): 3LL 6LO 2RM 3RM 4RM 5RM 6RM *)
  | 12, 0 => Some (mkAction 3 DL (Some 11))
  | 12, 1 => Some (mkAction 6 DL (Some 14))
  | 12, 2 => Some (mkAction 2 DR (Some 12))
  | 12, 3 => Some (mkAction 3 DR (Some 12))
  | 12, 4 => Some (mkAction 4 DR (Some 12))
  | 12, 5 => Some (mkAction 5 DR (Some 12))
  | 12, 6 => Some (mkAction 6 DR (Some 12))
  (* State N (13): 1RB 1LN 2LN 3LN 1LO 5LN 4RE *)
  | 13, 0 => Some (mkAction 1 DR (Some 1))
  | 13, 1 => Some (mkAction 1 DL (Some 13))
  | 13, 2 => Some (mkAction 2 DL (Some 13))
  | 13, 3 => Some (mkAction 3 DL (Some 13))
  | 13, 4 => Some (mkAction 1 DL (Some 14))
  | 13, 5 => Some (mkAction 5 DL (Some 13))
  | 13, 6 => Some (mkAction 4 DR (Some 4))
  (* State O (14): 1RB 4RP 1RK 0RM 4LN 0RQ 6LN *)
  | 14, 0 => Some (mkAction 1 DR (Some 1))
  | 14, 1 => Some (mkAction 4 DR (Some 15))
  | 14, 2 => Some (mkAction 1 DR (Some 10))
  | 14, 3 => Some (mkAction 0 DR (Some 12))
  | 14, 4 => Some (mkAction 4 DL (Some 13))
  | 14, 5 => Some (mkAction 0 DR (Some 16))
  | 14, 6 => Some (mkAction 6 DL (Some 13))
  (* State P (15): 4LJ 1RP 2RP 3RP 0RP 5RP 6RP *)
  | 15, 0 => Some (mkAction 4 DL (Some 9))
  | 15, 1 => Some (mkAction 1 DR (Some 15))
  | 15, 2 => Some (mkAction 2 DR (Some 15))
  | 15, 3 => Some (mkAction 3 DR (Some 15))
  | 15, 4 => Some (mkAction 0 DR (Some 15))
  | 15, 5 => Some (mkAction 5 DR (Some 15))
  | 15, 6 => Some (mkAction 6 DR (Some 15))
  (* State Q (16): 5LR --- 2RQ 3RQ 4RQ 5RQ 6RQ *)
  | 16, 0 => Some (mkAction 5 DL (Some 17))
  | 16, 2 => Some (mkAction 2 DR (Some 16))
  | 16, 3 => Some (mkAction 3 DR (Some 16))
  | 16, 4 => Some (mkAction 4 DR (Some 16))
  | 16, 5 => Some (mkAction 5 DR (Some 16))
  | 16, 6 => Some (mkAction 6 DR (Some 16))
  (* State R (17): 5RO --- 2LR 3LR 4LR 5LR 6LR *)
  | 17, 0 => Some (mkAction 5 DR (Some 14))
  | 17, 2 => Some (mkAction 2 DL (Some 17))
  | 17, 3 => Some (mkAction 3 DL (Some 17))
  | 17, 4 => Some (mkAction 4 DL (Some 17))
  | 17, 5 => Some (mkAction 5 DL (Some 17))
  | 17, 6 => Some (mkAction 6 DL (Some 17))
  (* State S (18): 1RB 4RT 2LS 3LS 4LS 5LS --- *)
  | 18, 0 => Some (mkAction 1 DR (Some 1))
  | 18, 1 => Some (mkAction 4 DR (Some 19))
  | 18, 2 => Some (mkAction 2 DL (Some 18))
  | 18, 3 => Some (mkAction 3 DL (Some 18))
  | 18, 4 => Some (mkAction 4 DL (Some 18))
  | 18, 5 => Some (mkAction 5 DL (Some 18))
  (* State T (19): 2LS --- 2RT 3RT 4RT 5RT --- *)
  | 19, 0 => Some (mkAction 2 DL (Some 18))
  | 19, 2 => Some (mkAction 2 DR (Some 19))
  | 19, 3 => Some (mkAction 3 DR (Some 19))
  | 19, 4 => Some (mkAction 4 DR (Some 19))
  | 19, 5 => Some (mkAction 5 DR (Some 19))
  (* State U (20): --- --- --- 4RA 6RH --- --- *)
  | 20, 3 => Some (mkAction 4 DR (Some 0))
  | 20, 4 => Some (mkAction 6 DR (Some 7))
  | _, _ => None
  end.

Lemma bb21_7_valid : ValidTM 21 7 bb21_7.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 21 (destruct s as [| s]; [ do 7 (destruct sym as [| sym]; [ simpl; try exact I; lia |]); lia |]); lia.
  - do 21 (destruct s as [| s]; [ do 7 (destruct sym as [| sym]; [ try lia; reflexivity |]); reflexivity |]); reflexivity.
Qed.

Lemma bb21_7_core : Fe1_7Core bb21_7.
Proof.
  constructor; try reflexivity; try discriminate; intros _; try reflexivity; lia.
Qed.

Lemma bb21_7_boot :
  Reaches bb21_7 initConfig (mkCfgR (Some 1) (rep 2 1 []) (rep 24 5 [])) 395.
Proof.
  unfold Reaches; vm_compute; reflexivity.
Qed.

Theorem BB21_7_champion :
  ValidTM 21 7 bb21_7 /\
  exists t, HaltsIn bb21_7 initConfig t /\ f_epsilon1 21 < t.
Proof.
  split; [exact bb21_7_valid |].
  destruct (Fe1_7_halts bb21_7 2 24 bb21_7_core ltac:(lia) ltac:(lia))
    as [t_core [[cf [Hsteps Hst]] Hbound]].
  exists (395 + t_core). split.
  - exists cf; split; [eapply steps_add; [exact bb21_7_boot | exact Hsteps] | exact Hst].
  - simpl in Hbound; lia.
Qed.

Print Assumptions BB21_7_champion.
