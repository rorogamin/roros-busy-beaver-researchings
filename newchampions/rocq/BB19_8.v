(*
  rocq/BB19_8.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(19, 8):
    TM: 6LL---0RF0RD1LN6RF------_1RZ1RB2LC5LK1RB5LC7LK---_0LI4RC2RC3RC2RC5RC5RC5RC_1LE1RD2RD3RD6RF5RD6LJ7RQ_3LA1LE2LE3LE---5LE---6LN_0LG1RF2RF3RF6LJ5RF------_0RI0LH1LR3RI---5RP6RI---_2LA1LH2LH3LH7LP5LH5LA---_3RP---0LA0LI1LF2LR------_2RO5RO2LJ3LJ---5LJ1RF6RG_2LL7RD2RK3RK4RK5RK6RK---_3RO2RO2LL3LL4LL5LL6LL5RO_3LL4RO2RM3RM4RM5RM6RM---_1RB1LN2LN3LN1LO5LN7RE4LF_1RB4RP1RK0RM4LN7RQ6LN1LB_4LJ1RP2RP3RP0RP5RP6RP7LM_5LL---2RQ3RQ4RQ5RQ6RQ---_1RB4RS2LR3LR4LR5LR7LR4LN_2LR---2RS3RS4RS5RS------
    Core: fe1_8 @ step 218: 1^2 B> 5^12 0^inf
    Proved bound: ValidTM 19 8 bb19_8 /\ exists t, HaltsIn bb19_8 initConfig t /\ f_epsilon1 9 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fe1.
Import ListNotations.

Definition bb19_8 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6LL --- 0RF 0RD 1LN 6RF --- --- *)
  | 0, 0 => Some (mkAction 6 DL (Some 11))
  | 0, 2 => Some (mkAction 0 DR (Some 5))
  | 0, 3 => Some (mkAction 0 DR (Some 3))
  | 0, 4 => Some (mkAction 1 DL (Some 13))
  | 0, 5 => Some (mkAction 6 DR (Some 5))
  (* State B (1): 1RZ 1RB 2LC 5LK 1RB 5LC 7LK --- *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 1 DR (Some 1))
  | 1, 2 => Some (mkAction 2 DL (Some 2))
  | 1, 3 => Some (mkAction 5 DL (Some 10))
  | 1, 4 => Some (mkAction 1 DR (Some 1))
  | 1, 5 => Some (mkAction 5 DL (Some 2))
  | 1, 6 => Some (mkAction 7 DL (Some 10))
  (* State C (2): 0LI 4RC 2RC 3RC 2RC 5RC 5RC 5RC *)
  | 2, 0 => Some (mkAction 0 DL (Some 8))
  | 2, 1 => Some (mkAction 4 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 2))
  | 2, 3 => Some (mkAction 3 DR (Some 2))
  | 2, 4 => Some (mkAction 2 DR (Some 2))
  | 2, 5 => Some (mkAction 5 DR (Some 2))
  | 2, 6 => Some (mkAction 5 DR (Some 2))
  | 2, 7 => Some (mkAction 5 DR (Some 2))
  (* State D (3): 1LE 1RD 2RD 3RD 6RF 5RD 6LJ 7RQ *)
  | 3, 0 => Some (mkAction 1 DL (Some 4))
  | 3, 1 => Some (mkAction 1 DR (Some 3))
  | 3, 2 => Some (mkAction 2 DR (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  | 3, 4 => Some (mkAction 6 DR (Some 5))
  | 3, 5 => Some (mkAction 5 DR (Some 3))
  | 3, 6 => Some (mkAction 6 DL (Some 9))
  | 3, 7 => Some (mkAction 7 DR (Some 16))
  (* State E (4): 3LA 1LE 2LE 3LE --- 5LE --- 6LN *)
  | 4, 0 => Some (mkAction 3 DL (Some 0))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 2 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 7 => Some (mkAction 6 DL (Some 13))
  (* State F (5): 0LG 1RF 2RF 3RF 6LJ 5RF --- --- *)
  | 5, 0 => Some (mkAction 0 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 2 DR (Some 5))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 6 DL (Some 9))
  | 5, 5 => Some (mkAction 5 DR (Some 5))
  (* State G (6): 0RI 0LH 1LR 3RI --- 5RP 6RI --- *)
  | 6, 0 => Some (mkAction 0 DR (Some 8))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 2 => Some (mkAction 1 DL (Some 17))
  | 6, 3 => Some (mkAction 3 DR (Some 8))
  | 6, 5 => Some (mkAction 5 DR (Some 15))
  | 6, 6 => Some (mkAction 6 DR (Some 8))
  (* State H (7): 2LA 1LH 2LH 3LH 7LP 5LH 5LA --- *)
  | 7, 0 => Some (mkAction 2 DL (Some 0))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 2 DL (Some 7))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 4 => Some (mkAction 7 DL (Some 15))
  | 7, 5 => Some (mkAction 5 DL (Some 7))
  | 7, 6 => Some (mkAction 5 DL (Some 0))
  (* State I (8): 3RP --- 0LA 0LI 1LF 2LR --- --- *)
  | 8, 0 => Some (mkAction 3 DR (Some 15))
  | 8, 2 => Some (mkAction 0 DL (Some 0))
  | 8, 3 => Some (mkAction 0 DL (Some 8))
  | 8, 4 => Some (mkAction 1 DL (Some 5))
  | 8, 5 => Some (mkAction 2 DL (Some 17))
  (* State J (9): 2RO 5RO 2LJ 3LJ --- 5LJ 1RF 6RG *)
  | 9, 0 => Some (mkAction 2 DR (Some 14))
  | 9, 1 => Some (mkAction 5 DR (Some 14))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DL (Some 9))
  | 9, 6 => Some (mkAction 1 DR (Some 5))
  | 9, 7 => Some (mkAction 6 DR (Some 6))
  (* State K (10): 2LL 7RD 2RK 3RK 4RK 5RK 6RK --- *)
  | 10, 0 => Some (mkAction 2 DL (Some 11))
  | 10, 1 => Some (mkAction 7 DR (Some 3))
  | 10, 2 => Some (mkAction 2 DR (Some 10))
  | 10, 3 => Some (mkAction 3 DR (Some 10))
  | 10, 4 => Some (mkAction 4 DR (Some 10))
  | 10, 5 => Some (mkAction 5 DR (Some 10))
  | 10, 6 => Some (mkAction 6 DR (Some 10))
  (* State L (11): 3RO 2RO 2LL 3LL 4LL 5LL 6LL 5RO *)
  | 11, 0 => Some (mkAction 3 DR (Some 14))
  | 11, 1 => Some (mkAction 2 DR (Some 14))
  | 11, 2 => Some (mkAction 2 DL (Some 11))
  | 11, 3 => Some (mkAction 3 DL (Some 11))
  | 11, 4 => Some (mkAction 4 DL (Some 11))
  | 11, 5 => Some (mkAction 5 DL (Some 11))
  | 11, 6 => Some (mkAction 6 DL (Some 11))
  | 11, 7 => Some (mkAction 5 DR (Some 14))
  (* State M (12): 3LL 4RO 2RM 3RM 4RM 5RM 6RM --- *)
  | 12, 0 => Some (mkAction 3 DL (Some 11))
  | 12, 1 => Some (mkAction 4 DR (Some 14))
  | 12, 2 => Some (mkAction 2 DR (Some 12))
  | 12, 3 => Some (mkAction 3 DR (Some 12))
  | 12, 4 => Some (mkAction 4 DR (Some 12))
  | 12, 5 => Some (mkAction 5 DR (Some 12))
  | 12, 6 => Some (mkAction 6 DR (Some 12))
  (* State N (13): 1RB 1LN 2LN 3LN 1LO 5LN 7RE 4LF *)
  | 13, 0 => Some (mkAction 1 DR (Some 1))
  | 13, 1 => Some (mkAction 1 DL (Some 13))
  | 13, 2 => Some (mkAction 2 DL (Some 13))
  | 13, 3 => Some (mkAction 3 DL (Some 13))
  | 13, 4 => Some (mkAction 1 DL (Some 14))
  | 13, 5 => Some (mkAction 5 DL (Some 13))
  | 13, 6 => Some (mkAction 7 DR (Some 4))
  | 13, 7 => Some (mkAction 4 DL (Some 5))
  (* State O (14): 1RB 4RP 1RK 0RM 4LN 7RQ 6LN 1LB *)
  | 14, 0 => Some (mkAction 1 DR (Some 1))
  | 14, 1 => Some (mkAction 4 DR (Some 15))
  | 14, 2 => Some (mkAction 1 DR (Some 10))
  | 14, 3 => Some (mkAction 0 DR (Some 12))
  | 14, 4 => Some (mkAction 4 DL (Some 13))
  | 14, 5 => Some (mkAction 7 DR (Some 16))
  | 14, 6 => Some (mkAction 6 DL (Some 13))
  | 14, 7 => Some (mkAction 1 DL (Some 1))
  (* State P (15): 4LJ 1RP 2RP 3RP 0RP 5RP 6RP 7LM *)
  | 15, 0 => Some (mkAction 4 DL (Some 9))
  | 15, 1 => Some (mkAction 1 DR (Some 15))
  | 15, 2 => Some (mkAction 2 DR (Some 15))
  | 15, 3 => Some (mkAction 3 DR (Some 15))
  | 15, 4 => Some (mkAction 0 DR (Some 15))
  | 15, 5 => Some (mkAction 5 DR (Some 15))
  | 15, 6 => Some (mkAction 6 DR (Some 15))
  | 15, 7 => Some (mkAction 7 DL (Some 12))
  (* State Q (16): 5LL --- 2RQ 3RQ 4RQ 5RQ 6RQ --- *)
  | 16, 0 => Some (mkAction 5 DL (Some 11))
  | 16, 2 => Some (mkAction 2 DR (Some 16))
  | 16, 3 => Some (mkAction 3 DR (Some 16))
  | 16, 4 => Some (mkAction 4 DR (Some 16))
  | 16, 5 => Some (mkAction 5 DR (Some 16))
  | 16, 6 => Some (mkAction 6 DR (Some 16))
  (* State R (17): 1RB 4RS 2LR 3LR 4LR 5LR 7LR 4LN *)
  | 17, 0 => Some (mkAction 1 DR (Some 1))
  | 17, 1 => Some (mkAction 4 DR (Some 18))
  | 17, 2 => Some (mkAction 2 DL (Some 17))
  | 17, 3 => Some (mkAction 3 DL (Some 17))
  | 17, 4 => Some (mkAction 4 DL (Some 17))
  | 17, 5 => Some (mkAction 5 DL (Some 17))
  | 17, 6 => Some (mkAction 7 DL (Some 17))
  | 17, 7 => Some (mkAction 4 DL (Some 13))
  (* State S (18): 2LR --- 2RS 3RS 4RS 5RS --- --- *)
  | 18, 0 => Some (mkAction 2 DL (Some 17))
  | 18, 2 => Some (mkAction 2 DR (Some 18))
  | 18, 3 => Some (mkAction 3 DR (Some 18))
  | 18, 4 => Some (mkAction 4 DR (Some 18))
  | 18, 5 => Some (mkAction 5 DR (Some 18))
  | _, _ => None
  end.

Lemma bb19_8_valid : ValidTM 19 8 bb19_8.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 19 (destruct s as [| s]; [ do 8 (destruct sym as [| sym]; [ simpl; try exact I; lia |]); lia |]); lia.
  - do 19 (destruct s as [| s]; [ do 8 (destruct sym as [| sym]; [ try lia; reflexivity |]); reflexivity |]); reflexivity.
Qed.

Lemma bb19_8_core : Fe1_8Core bb19_8.
Proof.
  constructor; try reflexivity; try discriminate; intros _; try reflexivity; lia.
Qed.

Lemma bb19_8_boot :
  Reaches bb19_8 initConfig (mkCfgR (Some 1) (rep 2 1 []) (rep 12 5 [])) 218.
Proof.
  unfold Reaches; vm_compute; reflexivity.
Qed.

Theorem BB19_8_champion :
  ValidTM 19 8 bb19_8 /\
  exists t, HaltsIn bb19_8 initConfig t /\ f_epsilon1 9 < t.
Proof.
  split; [exact bb19_8_valid |].
  destruct (Fe1_8_halts bb19_8 2 12 bb19_8_core ltac:(lia) ltac:(lia))
    as [t_core [[cf [Hsteps Hst]] Hbound]].
  exists (218 + t_core). split.
  - exists cf; split; [eapply steps_add; [exact bb19_8_boot | exact Hsteps] | exact Hst].
  - simpl in Hbound; lia.
Qed.

Print Assumptions BB19_8_champion.
