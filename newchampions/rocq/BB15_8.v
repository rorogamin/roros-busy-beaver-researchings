From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_8_Peeker.
Import ListNotations.

Definition bb15_8 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 6 DL (Some 3))
  | 0, 1 => Some (mkAction 5 DR (Some 0))
  | 0, 2 => Some (mkAction 2 DL (Some 8))
  | 0, 3 => Some (mkAction 6 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DR (Some 5))
  | 0, 7 => Some (mkAction 7 DR (Some 0))
  | 1, 0 => Some (mkAction 7 DR (Some 0))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  | 1, 4 => Some (mkAction 4 DL (Some 5))
  | 1, 5 => Some (mkAction 0 DL (Some 2))
  | 1, 6 => Some (mkAction 2 DL (Some 3))
  | 1, 7 => Some (mkAction 7 DL (Some 1))
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 2))
  | 2, 6 => Some (mkAction 3 DL (Some 2))
  | 2, 7 => Some (mkAction 1 DL (Some 1))
  | 3, 0 => Some (mkAction 7 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 4 DL (Some 3))
  | 3, 5 => Some (mkAction 1 DL (Some 3))
  | 3, 6 => Some (mkAction 3 DL (Some 3))
  | 3, 7 => Some (mkAction 3 DL (Some 1))
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 7 DR (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 8))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 6 => Some (mkAction 7 DR (Some 2))
  | 4, 7 => Some (mkAction 7 DR (Some 4))
  | 5, 0 => Some (mkAction 1 DL (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 1))
  | 5, 3 => Some (mkAction 6 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 1))
  | 5, 5 => Some (mkAction 1 DL (Some 5))
  | 5, 6 => Some (mkAction 3 DL (Some 5))
  | 5, 7 => Some (mkAction 3 DL (Some 4))
  | 6, 0 => Some (mkAction 3 DR (Some 1))
  | 6, 1 => Some (mkAction 1 DL (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 6))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 7, 0 => Some (mkAction 1 DR (None))
  | 7, 1 => Some (mkAction 3 DL (Some 1))
  | 7, 2 => Some (mkAction 4 DL (Some 4))
  | 7, 3 => Some (mkAction 2 DR (Some 7))
  | 7, 4 => Some (mkAction 3 DL (Some 6))
  | 7, 5 => Some (mkAction 2 DL (Some 9))
  | 7, 6 => Some (mkAction 5 DL (Some 10))
  | 7, 7 => Some (mkAction 2 DR (Some 12))
  | 8, 0 => Some (mkAction 3 DR (Some 8))
  | 8, 1 => Some (mkAction 3 DL (Some 1))
  | 8, 2 => Some (mkAction 2 DR (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 8, 4 => Some (mkAction 7 DL (Some 14))
  | 8, 5 => Some (mkAction 0 DR (Some 2))
  | 8, 7 => Some (mkAction 4 DR (Some 8))
  | 9, 0 => Some (mkAction 0 DR (Some 2))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 2 DL (Some 9))
  | 10, 0 => Some (mkAction 3 DR (Some 10))
  | 10, 2 => Some (mkAction 5 DL (Some 10))
  | 10, 3 => Some (mkAction 5 DL (Some 10))
  | 10, 4 => Some (mkAction 7 DL (Some 10))
  | 10, 5 => Some (mkAction 2 DR (Some 7))
  | 10, 7 => Some (mkAction 2 DL (Some 1))
  | 11, 0 => Some (mkAction 3 DR (Some 11))
  | 11, 2 => Some (mkAction 6 DL (Some 11))
  | 11, 3 => Some (mkAction 6 DL (Some 11))
  | 11, 6 => Some (mkAction 2 DR (Some 7))
  | 12, 0 => Some (mkAction 1 DR (None))
  | 12, 5 => Some (mkAction 6 DL (Some 14))
  | 12, 6 => Some (mkAction 7 DL (Some 13))
  | 12, 7 => Some (mkAction 6 DL (Some 11))
  | 13, 0 => Some (mkAction 3 DR (Some 13))
  | 13, 2 => Some (mkAction 7 DL (Some 13))
  | 13, 3 => Some (mkAction 7 DL (Some 13))
  | 13, 6 => Some (mkAction 2 DR (Some 14))
  | 13, 7 => Some (mkAction 2 DR (Some 7))
  | 14, 0 => Some (mkAction 3 DR (Some 13))
  | 14, 2 => Some (mkAction 6 DL (Some 14))
  | 14, 3 => Some (mkAction 6 DL (Some 14))
  | 14, 4 => Some (mkAction 2 DL (Some 8))
  | 14, 6 => Some (mkAction 2 DR (Some 12))
  | 14, 7 => Some (mkAction 7 DL (Some 8))
  | _, _ => None
  end.

Lemma bb15_8_valid : ValidTM 15 8 bb15_8.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb15_8_core : Fwpw_8Core bb15_8. Proof. constructor; reflexivity. Qed.
Lemma bb15_8_i : Fwpw_8_ICore bb15_8. Proof. constructor; [exact bb15_8_core | ..]; reflexivity. Qed.
Lemma bb15_8_j : Fwpw_8_JCore bb15_8. Proof. constructor; [exact bb15_8_i | ..]; reflexivity. Qed.
Lemma bb15_8_k : Fwpw_8_KCore bb15_8. Proof. constructor; [exact bb15_8_j | ..]; reflexivity. Qed.
Lemma bb15_8_pn : Fwpw_8_PeekerNCore bb15_8. Proof. constructor; [exact bb15_8_k | ..]; reflexivity. Qed.
Lemma bb15_8_po : Fwpw_8_PeekerOCore bb15_8. Proof. constructor; [exact bb15_8_pn | ..]; reflexivity. Qed.

Lemma bb15_8_init :
  Reaches bb15_8 initConfig (H8cfg 9 1 (rep 3 2 (7 :: rep 8 5 []))) 182.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB15_8_champion :
  ValidTM 15 8 bb15_8 /\
  exists t, HaltsIn bb15_8 initConfig t /\ f_omega_omega_plus 6 8 < t.
Proof.
  split; [exact bb15_8_valid |].
  pose proof bb15_8_init as H0.
  destruct (StepFOdd_rep bb15_8 2 (f_omega_omega) f_omega_omega_props (w8_stepFOdd_2 bb15_8 bb15_8_i) 3 9 (7 :: rep 8 5 []) ltac:(lia) (ex_intro _ 4 eq_refl)) as [n1 [t1 [H1 [Hinc1 [Hf1 [_ Ho1]]]]]].
  destruct (StepF7Odd_rep bb15_8 5 (f_omega_omega_plus 5) (fPlus_props _ f_omega_omega_props 5) (w8_peeker_5_odd bb15_8 bb15_8_po) 8 n1 [] ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [Hf2 [Ht2 _]]]]]].
  assert (Hhalt1 : Reaches bb15_8 (H8cfg n2 1 [7]) (mkCfgR (Some 12) (2 :: 2 :: rep n2 3 []) []) 1) by (unfold H8cfg; apply steps_one; reflexivity).
  assert (Hhalt2 : Reaches bb15_8 (mkCfgR (Some 12) (2 :: 2 :: rep n2 3 []) []) (mkCfgR None (1 :: 2 :: 2 :: rep n2 3 []) []) 1) by (apply steps_one; reflexivity).
  exists (182 + t1 + t2 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: 2 :: rep n2 3 []) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact Hhalt1] | exact Hhalt2].
  -     assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf1 3 ltac:(lia) ltac:(lia)) as Hbase1.
    pose proof f_omega_omega_3_ge_40 as H40.
    assert (Hge_prev : 4 * 8 <= n1 - 2).
    { rewrite !iter_succ, iter_zero in Hbase1.
       pose proof (fgh_ge_self _ f_omega_omega_props (f_omega_omega 3)).
       pose proof (fgh_ge_self _ f_omega_omega_props (f_omega_omega (f_omega_omega 3))). lia. }
    pose proof (Hf2 8 ltac:(lia) Hge_prev) as Hfinal.
    specialize (Ht2 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB15_8_champion.
