(*
  rocq/BB16_6.v
  Formal, axiom-free Rocq 9.1 proof of Busy Beaver Champion BB(16, 6):
    TM: 2RH5RH0RF0RD1LN---_1RZ1RB2LC1RA------_0LI4RC2RC3RC2RC2RC_1LE1RD2RD3RD2LN---_3LA1LE2LE3LE------_0LG1RF2RF3RF5RP---_0RI0LH4LK3RI------_2LA1LH2LH3LH---3LP_3RP3LM0LA0LI0LK---_2RO---2LJ3LJ---5RK_2LL---2RK3RK4RK---_3RO2RO2LL3LL4LL4LC_3LL4RC2RM3RM4RM---_1RB1LN2LN3LN1LO2RE_1RB4RP1RK0RM4LN---_4LJ1RP2RP3RP0RP---
    Core: fe0_5_16 @ step 184: 1^4 B> 2^14 0^inf
    Proved bound: ValidTM 16 6 bb16_6 /\ exists t, HaltsIn bb16_6 initConfig t /\ f_epsilon0 11 < t
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fe1.
Import ListNotations.

Definition bb16_6 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2RH 5RH 0RF 0RD 1LN --- *)
  | 0, 0 => Some (mkAction 2 DR (Some 7))
  | 0, 1 => Some (mkAction 5 DR (Some 7))
  | 0, 2 => Some (mkAction 0 DR (Some 5))
  | 0, 3 => Some (mkAction 0 DR (Some 3))
  | 0, 4 => Some (mkAction 1 DL (Some 13))
  (* State B (1): 1RZ 1RB 2LC 1RA --- --- *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 1 DR (Some 1))
  | 1, 2 => Some (mkAction 2 DL (Some 2))
  | 1, 3 => Some (mkAction 1 DR (Some 0))
  (* State C (2): 0LI 4RC 2RC 3RC 2RC 2RC *)
  | 2, 0 => Some (mkAction 0 DL (Some 8))
  | 2, 1 => Some (mkAction 4 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 2))
  | 2, 3 => Some (mkAction 3 DR (Some 2))
  | 2, 4 => Some (mkAction 2 DR (Some 2))
  | 2, 5 => Some (mkAction 2 DR (Some 2))
  (* State D (3): 1LE 1RD 2RD 3RD 2LN --- *)
  | 3, 0 => Some (mkAction 1 DL (Some 4))
  | 3, 1 => Some (mkAction 1 DR (Some 3))
  | 3, 2 => Some (mkAction 2 DR (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  | 3, 4 => Some (mkAction 2 DL (Some 13))
  (* State E (4): 3LA 1LE 2LE 3LE --- --- *)
  | 4, 0 => Some (mkAction 3 DL (Some 0))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 2 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  (* State F (5): 0LG 1RF 2RF 3RF 5RP --- *)
  | 5, 0 => Some (mkAction 0 DL (Some 6))
  | 5, 1 => Some (mkAction 1 DR (Some 5))
  | 5, 2 => Some (mkAction 2 DR (Some 5))
  | 5, 3 => Some (mkAction 3 DR (Some 5))
  | 5, 4 => Some (mkAction 5 DR (Some 15))
  (* State G (6): 0RI 0LH 4LK 3RI --- --- *)
  | 6, 0 => Some (mkAction 0 DR (Some 8))
  | 6, 1 => Some (mkAction 0 DL (Some 7))
  | 6, 2 => Some (mkAction 4 DL (Some 10))
  | 6, 3 => Some (mkAction 3 DR (Some 8))
  (* State H (7): 2LA 1LH 2LH 3LH --- 3LP *)
  | 7, 0 => Some (mkAction 2 DL (Some 0))
  | 7, 1 => Some (mkAction 1 DL (Some 7))
  | 7, 2 => Some (mkAction 2 DL (Some 7))
  | 7, 3 => Some (mkAction 3 DL (Some 7))
  | 7, 5 => Some (mkAction 3 DL (Some 15))
  (* State I (8): 3RP 3LM 0LA 0LI 0LK --- *)
  | 8, 0 => Some (mkAction 3 DR (Some 15))
  | 8, 1 => Some (mkAction 3 DL (Some 12))
  | 8, 2 => Some (mkAction 0 DL (Some 0))
  | 8, 3 => Some (mkAction 0 DL (Some 8))
  | 8, 4 => Some (mkAction 0 DL (Some 10))
  (* State J (9): 2RO --- 2LJ 3LJ --- 5RK *)
  | 9, 0 => Some (mkAction 2 DR (Some 14))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DR (Some 10))
  (* State K (10): 2LL --- 2RK 3RK 4RK --- *)
  | 10, 0 => Some (mkAction 2 DL (Some 11))
  | 10, 2 => Some (mkAction 2 DR (Some 10))
  | 10, 3 => Some (mkAction 3 DR (Some 10))
  | 10, 4 => Some (mkAction 4 DR (Some 10))
  (* State L (11): 3RO 2RO 2LL 3LL 4LL 4LC *)
  | 11, 0 => Some (mkAction 3 DR (Some 14))
  | 11, 1 => Some (mkAction 2 DR (Some 14))
  | 11, 2 => Some (mkAction 2 DL (Some 11))
  | 11, 3 => Some (mkAction 3 DL (Some 11))
  | 11, 4 => Some (mkAction 4 DL (Some 11))
  | 11, 5 => Some (mkAction 4 DL (Some 2))
  (* State M (12): 3LL 4RC 2RM 3RM 4RM --- *)
  | 12, 0 => Some (mkAction 3 DL (Some 11))
  | 12, 1 => Some (mkAction 4 DR (Some 2))
  | 12, 2 => Some (mkAction 2 DR (Some 12))
  | 12, 3 => Some (mkAction 3 DR (Some 12))
  | 12, 4 => Some (mkAction 4 DR (Some 12))
  (* State N (13): 1RB 1LN 2LN 3LN 1LO 2RE *)
  | 13, 0 => Some (mkAction 1 DR (Some 1))
  | 13, 1 => Some (mkAction 1 DL (Some 13))
  | 13, 2 => Some (mkAction 2 DL (Some 13))
  | 13, 3 => Some (mkAction 3 DL (Some 13))
  | 13, 4 => Some (mkAction 1 DL (Some 14))
  | 13, 5 => Some (mkAction 2 DR (Some 4))
  (* State O (14): 1RB 4RP 1RK 0RM 4LN --- *)
  | 14, 0 => Some (mkAction 1 DR (Some 1))
  | 14, 1 => Some (mkAction 4 DR (Some 15))
  | 14, 2 => Some (mkAction 1 DR (Some 10))
  | 14, 3 => Some (mkAction 0 DR (Some 12))
  | 14, 4 => Some (mkAction 4 DL (Some 13))
  (* State P (15): 4LJ 1RP 2RP 3RP 0RP --- *)
  | 15, 0 => Some (mkAction 4 DL (Some 9))
  | 15, 1 => Some (mkAction 1 DR (Some 15))
  | 15, 2 => Some (mkAction 2 DR (Some 15))
  | 15, 3 => Some (mkAction 3 DR (Some 15))
  | 15, 4 => Some (mkAction 0 DR (Some 15))
  | _, _ => None
  end.

Lemma bb16_6_valid : ValidTM 16 6 bb16_6.
Proof.
  split; intros s sym H1.
  - intro H2.
    do 16 (destruct s as [| s]; [ do 6 (destruct sym as [| sym]; [ simpl; try exact I; lia |]); lia |]); lia.
  - do 16 (destruct s as [| s]; [ do 6 (destruct sym as [| sym]; [ try lia; reflexivity |]); reflexivity |]); reflexivity.
Qed.

Lemma bb16_6_core : Fe0_5_16Core bb16_6.
Proof.
  constructor; try reflexivity; try discriminate; intros _; try reflexivity; lia.
Qed.

Lemma bb16_6_boot :
  Reaches bb16_6 initConfig (mkCfgR (Some 1) (rep 4 1 []) (rep 14 2 [])) 184.
Proof.
  unfold Reaches; vm_compute; reflexivity.
Qed.

Theorem BB16_6_champion :
  ValidTM 16 6 bb16_6 /\
  exists t, HaltsIn bb16_6 initConfig t /\ f_epsilon0 11 < t.
Proof.
  split; [exact bb16_6_valid |].
  destruct (Fe0_5_16_halts bb16_6 4 14 bb16_6_core ltac:(lia) ltac:(lia))
    as [t_core [[cf [Hsteps Hst]] Hbound]].
  exists (184 + t_core). split.
  - exists cf; split; [eapply steps_add; [exact bb16_6_boot | exact Hsteps] | exact Hst].
  - simpl in Hbound; lia.
Qed.

Print Assumptions BB16_6_champion.
