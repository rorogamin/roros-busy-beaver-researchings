From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder.
Import ListNotations.

Definition bb11_9 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 8 DL (Some 10))
  | 0, 1 => Some (mkAction 5 DR (Some 0))
  | 0, 3 => Some (mkAction 6 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DR (Some 5))
  | 0, 7 => Some (mkAction 7 DR (Some 0))
  | 0, 8 => Some (mkAction 7 DR (Some 6))
  | 1, 0 => Some (mkAction 7 DR (Some 0))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  | 1, 4 => Some (mkAction 4 DL (Some 5))
  | 1, 5 => Some (mkAction 0 DL (Some 2))
  | 1, 6 => Some (mkAction 2 DL (Some 3))
  | 1, 7 => Some (mkAction 7 DL (Some 1))
  | 1, 8 => Some (mkAction 2 DR (Some 9))
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
  | 5, 8 => Some (mkAction 6 DL (Some 10))
  | 6, 0 => Some (mkAction 3 DR (Some 1))
  | 6, 1 => Some (mkAction 1 DL (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 6))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 6 => Some (mkAction 3 DL (Some 6))
  | 6, 7 => Some (mkAction 2 DL (Some 3))
  | 7, 0 => Some (mkAction 1 DR (None))
  | 7, 1 => Some (mkAction 3 DL (Some 1))
  | 7, 2 => Some (mkAction 4 DL (Some 4))
  | 7, 3 => Some (mkAction 2 DR (Some 7))
  | 7, 4 => Some (mkAction 3 DL (Some 6))
  | 7, 5 => Some (mkAction 2 DL (Some 9))
  | 7, 6 => Some (mkAction 5 DL (Some 10))
  | 7, 7 => Some (mkAction 2 DL (Some 3))
  | 7, 8 => Some (mkAction 1 DR (Some 6))
  | 8, 0 => Some (mkAction 3 DR (Some 8))
  | 8, 1 => Some (mkAction 3 DL (Some 1))
  | 8, 2 => Some (mkAction 2 DR (Some 8))
  | 8, 3 => Some (mkAction 2 DL (Some 8))
  | 9, 0 => Some (mkAction 0 DR (Some 2))
  | 9, 1 => Some (mkAction 1 DR (Some 2))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 2 DL (Some 9))
  | 10, 0 => Some (mkAction 3 DR (Some 10))
  | 10, 2 => Some (mkAction 5 DL (Some 10))
  | 10, 3 => Some (mkAction 5 DL (Some 10))
  | 10, 4 => Some (mkAction 8 DL (Some 5))
  | 10, 5 => Some (mkAction 2 DR (Some 7))
  | 10, 7 => Some (mkAction 0 DL (Some 6))
  | 10, 8 => Some (mkAction 8 DR (Some 5))
  | _, _ => None
  end.

Lemma bb11_9_valid : ValidTM 11 9 bb11_9.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb11_9_core : Fwpw_8Core bb11_9. Proof. constructor; reflexivity. Qed.
Lemma bb11_9_i : Fwpw_8_ICore bb11_9. Proof. constructor; [exact bb11_9_core | ..]; reflexivity. Qed.
Lemma bb11_9_j : Fwpw_8_JCore bb11_9. Proof. constructor; [exact bb11_9_i | ..]; reflexivity. Qed.
Lemma bb11_9_k : Fwpw_8_KCore bb11_9. Proof. constructor; [exact bb11_9_j | ..]; reflexivity. Qed.

Lemma bb11_9_init :
  Reaches bb11_9 initConfig (H8cfg 9 1 (rep 1 2 (rep 4 5 (rep 35 6 [])))) 1466.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB11_9_champion :
  ValidTM 11 9 bb11_9 /\
  exists t, HaltsIn bb11_9 initConfig t /\ f_omega_omega_plus 3 35 < t.
Proof.
  split; [exact bb11_9_valid |].
  pose proof bb11_9_init as H0.
  destruct (StepF_rep bb11_9 2 (f_omega_omega) f_omega_omega_props (w8_stepF_2 bb11_9 bb11_9_i) 1 9 (rep 4 5 (rep 35 6 [])) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [Hf1 _]]]]].
  destruct (StepF_rep bb11_9 5 (f_omega_omega_plus 1) (fPlus_props _ f_omega_omega_props 1) (w8_stepF_5 bb11_9 bb11_9_j) 4 n1 (rep 35 6 []) ltac:(lia)) as [n2 [t2 [H2 [Hinc2 [Hf2 _]]]]].
  destruct (StepF_rep bb11_9 6 (f_omega_omega_plus 2) (fPlus_props _ f_omega_omega_props 2) (w8_stepF_6 bb11_9 bb11_9_k) 35 n2 [] ltac:(lia)) as [n3 [t3 [H3 [Hinc3 [Hf3 Ht3]]]]].
  assert (Hhalt : Reaches bb11_9 (H8cfg n3 1 []) (mkCfgR None (1 :: 2 :: rep n3 3 []) []) 1) by (unfold H8cfg; apply steps_one; reflexivity).
  exists (1466 + t1 + t2 + t3 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: rep n3 3 []) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact Hhalt].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf1 3 ltac:(lia) ltac:(lia)) as Hbase1.
    pose proof f_omega_omega_3_ge_40 as H40.
    assert (Hge_prev : 2 * 35 <= n2 - 2).
    { rewrite !iter_succ, iter_zero in Hbase1; pose proof (fgh_ge_self _ f_omega_omega_props (f_omega_omega 3)); lia. }
    pose proof (Hf3 35 ltac:(lia) Hge_prev) as Hfinal.
    specialize (Ht3 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB11_9_champion.
