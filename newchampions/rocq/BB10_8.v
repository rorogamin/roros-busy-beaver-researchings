From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder.
Import ListNotations.

Definition bb10_8 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 5 DL (Some 9))
  | 0, 1 => Some (mkAction 5 DR (Some 0))
  | 0, 2 => Some (mkAction 4 DL (Some 8))
  | 0, 3 => Some (mkAction 6 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DR (Some 5))
  | 0, 5 => Some (mkAction 5 DL (Some 9))
  | 0, 6 => Some (mkAction 6 DR (Some 3))
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
  | 3, 1 => Some (mkAction 6 DR (Some 4))
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
  | 4, 4 => Some (mkAction 7 DL (Some 3))
  | 4, 5 => Some (mkAction 6 DL (Some 9))
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
  | 6, 5 => Some (mkAction 1 DL (Some 3))
  | 6, 6 => Some (mkAction 2 DL (Some 2))
  | 6, 7 => Some (mkAction 6 DL (Some 2))
  | 7, 0 => Some (mkAction 1 DR (None))
  | 7, 1 => Some (mkAction 3 DL (Some 1))
  | 7, 2 => Some (mkAction 4 DL (Some 4))
  | 7, 3 => Some (mkAction 2 DR (Some 7))
  | 7, 4 => Some (mkAction 3 DL (Some 6))
  | 7, 5 => Some (mkAction 2 DL (Some 9))
  | 8, 0 => Some (mkAction 3 DR (Some 8))
  | 8, 1 => Some (mkAction 3 DL (Some 1))
  | 8, 2 => Some (mkAction 2 DR (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 8, 5 => Some (mkAction 1 DR (Some 4))
  | 9, 0 => Some (mkAction 0 DR (Some 2))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 2 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DL (Some 6))
  | 9, 6 => Some (mkAction 5 DL (Some 1))
  | 9, 7 => Some (mkAction 5 DR (Some 9))
  | _, _ => None
  end.

Lemma bb10_8_valid : ValidTM 10 8 bb10_8.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|s]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|sym]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb10_8_core : Fwpw_8Core bb10_8. Proof. constructor; reflexivity. Qed.
Lemma bb10_8_i : Fwpw_8_ICore bb10_8. Proof. constructor; [exact bb10_8_core | ..]; reflexivity. Qed.
Lemma bb10_8_j : Fwpw_8_JCore bb10_8. Proof. constructor; [exact bb10_8_i | ..]; reflexivity. Qed.

Lemma bb10_8_init :
  Reaches bb10_8 initConfig (H8cfg 9 1 (rep 2 2 (rep 28 5 []))) 401.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB10_8_champion :
  ValidTM 10 8 bb10_8 /\
  exists t, HaltsIn bb10_8 initConfig t /\ f_omega_omega_plus 2 28 < t.
Proof.
  split; [exact bb10_8_valid |].
  pose proof bb10_8_init as H0.
  destruct (StepF_rep bb10_8 2 (f_omega_omega) f_omega_omega_props (w8_stepF_2 bb10_8 bb10_8_i) 2 9 (rep 28 5 []) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [Hf1 _]]]]].
  destruct (StepF_rep bb10_8 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) (w8_stepF_5 bb10_8 bb10_8_j) 28 n1 [] ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [Hf2 Ht2]]]]].
  assert (Hhalt : Reaches bb10_8 (H8cfg n2 1 []) (mkCfgR None (1 :: 2 :: rep n2 3 []) []) 1) by (unfold H8cfg; apply steps_one; reflexivity).
  exists (401 + t1 + t2 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n2 3 []) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf1 3 ltac:(lia) ltac:(lia)) as Hbase1.
    pose proof f_omega_omega_3_ge_40 as H40.
    assert (Hge_prev : 2 * 28 <= n1 - 2).
    { rewrite !iter_succ, iter_zero in Hbase1; pose proof (fgh_ge_self _ f_omega_omega_props (f_omega_omega 3)); lia. }
    pose proof (Hf2 28 ltac:(lia) Hge_prev) as Hfinal.
    specialize (Ht2 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB10_8_champion.
