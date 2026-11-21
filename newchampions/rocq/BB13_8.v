From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder.
Import ListNotations.

Definition bb13_8 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 7 DL (Some 8))
  | 0, 1 => Some (mkAction 5 DR (Some 0))
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
  | 7, 7 => Some (mkAction 6 DL (Some 11))
  | 8, 0 => Some (mkAction 3 DR (Some 8))
  | 8, 1 => Some (mkAction 3 DL (Some 1))
  | 8, 2 => Some (mkAction 2 DR (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 8, 7 => Some (mkAction 4 DR (Some 9))
  | 9, 0 => Some (mkAction 0 DR (Some 2))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 2 DL (Some 9))
  | 9, 7 => Some (mkAction 3 DL (Some 11))
  | 10, 0 => Some (mkAction 3 DR (Some 10))
  | 10, 2 => Some (mkAction 5 DL (Some 10))
  | 10, 3 => Some (mkAction 5 DL (Some 10))
  | 10, 5 => Some (mkAction 2 DR (Some 7))
  | 11, 0 => Some (mkAction 3 DR (Some 11))
  | 11, 2 => Some (mkAction 6 DL (Some 11))
  | 11, 3 => Some (mkAction 6 DL (Some 11))
  | 11, 4 => Some (mkAction 3 DR (Some 12))
  | 11, 6 => Some (mkAction 2 DR (Some 7))
  | 12, 0 => Some (mkAction 3 DR (Some 4))
  | 12, 1 => Some (mkAction 1 DL (Some 6))
  | 12, 3 => Some (mkAction 7 DL (Some 12))
  | 12, 4 => Some (mkAction 1 DR (Some 4))
  | 12, 7 => Some (mkAction 4 DR (Some 9))
  | _, _ => None
  end.

Lemma bb13_8_valid : ValidTM 13 8 bb13_8.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb13_8_core : Fwpw_8Core bb13_8. Proof. constructor; reflexivity. Qed.
Lemma bb13_8_i : Fwpw_8_ICore bb13_8. Proof. constructor; [exact bb13_8_core | ..]; reflexivity. Qed.
Lemma bb13_8_j : Fwpw_8_JCore bb13_8. Proof. constructor; [exact bb13_8_i | ..]; reflexivity. Qed.
Lemma bb13_8_k : Fwpw_8_KCore bb13_8. Proof. constructor; [exact bb13_8_j | ..]; reflexivity. Qed.
Lemma bb13_8_l : Fwpw_8_LCore bb13_8. Proof. constructor; [exact bb13_8_k | ..]; reflexivity. Qed.

Lemma bb13_8_init :
  Reaches bb13_8 initConfig (H8cfg 9 1 (rep 1 2 (rep 1 5 (rep 2 6 (rep 9 7 []))))) 200.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB13_8_champion :
  ValidTM 13 8 bb13_8 /\
  exists t, HaltsIn bb13_8 initConfig t /\ f_omega_omega_plus 4 9 < t.
Proof.
  split; [exact bb13_8_valid |].
  pose proof bb13_8_init as H0.
  destruct (StepF_rep bb13_8 2 (f_omega_omega) f_omega_omega_props (w8_stepF_2 bb13_8 bb13_8_i) 1 9 (rep 1 5 (rep 2 6 (rep 9 7 []))) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [Hf1 _]]]]].
  destruct (StepF_rep bb13_8 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) (w8_stepF_5 bb13_8 bb13_8_j) 1 n1 (rep 2 6 (rep 9 7 [])) ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [Hf2 _]]]]].
  destruct (StepF_rep bb13_8 6 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) (w8_stepF_6 bb13_8 bb13_8_k) 2 n2 (rep 9 7 []) ltac:(lia)) as [n3 [t3 [H3 [Hinc3 [Hf3 _]]]]].
  destruct (StepF_rep bb13_8 7 (f_omega_omega_plus 3) (fPlus_props _ f_omega_omega_props 3) (w8_stepF_7 bb13_8 bb13_8_l) 9 n3 [] ltac:(lia)) as [n4 [t4 [H4 [Hinc4 [Hf4 Ht4]]]]].
  assert (Hhalt : Reaches bb13_8 (H8cfg n4 1 []) (mkCfgR None (1 :: 2 :: rep n4 3 []) []) 1) by (unfold H8cfg; apply steps_one; reflexivity).
  exists (200 + t1 + t2 + t3 + t4 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n4 3 []) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf1 3 ltac:(lia) ltac:(lia)) as Hbase1.
    pose proof f_omega_omega_3_ge_40 as H40.
    assert (Hge_prev : 2 * 9 <= n3 - 2).
    { rewrite !iter_succ, iter_zero in Hbase1; pose proof (fgh_ge_self _ f_omega_omega_props (f_omega_omega 3)); lia. }
    pose proof (Hf4 9 ltac:(lia) Hge_prev) as Hfinal.
    specialize (Ht4 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB13_8_champion.
