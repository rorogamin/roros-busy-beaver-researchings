From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2_4 Fwp2_4_Ladder.
Import ListNotations.

Definition bb154 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 1 DL (Some 3))
  | 0, 1 => Some (mkAction 2 DR (Some 6))
  | 0, 2 => Some (mkAction 2 DL (Some 0))
  | 0, 3 => Some (mkAction 3 DL (Some 6))
  | 1, 1 => Some (mkAction 2 DL (Some 7))
  | 1, 2 => Some (mkAction 2 DR (Some 1))
  | 1, 3 => Some (mkAction 2 DR (Some 5))
  | 2, 0 => Some (mkAction 2 DL (Some 12))
  | 2, 1 => Some (mkAction 1 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 1))
  | 2, 3 => Some (mkAction 3 DL (Some 6))
  | 3, 0 => Some (mkAction 0 DR (Some 2))
  | 3, 1 => Some (mkAction 1 DR (Some 2))
  | 3, 2 => Some (mkAction 1 DL (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  | 4, 0 => Some (mkAction 3 DR (Some 3))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  | 5, 0 => Some (mkAction 1 DR (Some 8))
  | 5, 1 => Some (mkAction 3 DL (Some 3))
  | 5, 2 => Some (mkAction 2 DL (Some 4))
  | 5, 3 => Some (mkAction 3 DL (Some 4))
  | 6, 0 => Some (mkAction 1 DR (Some 6))
  | 6, 1 => Some (mkAction 1 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DR (Some 6))
  | 6, 3 => Some (mkAction 3 DL (Some 6))
  | 7, 0 => Some (mkAction 1 DR (Some 2))
  | 7, 1 => Some (mkAction 2 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 0))
  | 7, 3 => Some (mkAction 1 DL (Some 4))
  | 8, 0 => Some (mkAction 0 DL (Some 9))
  | 8, 1 => Some (mkAction 0 DL (Some 10))
  | 8, 2 => Some (mkAction 1 DL (Some 11))
  | 8, 3 => Some (mkAction 3 DR (Some 12))
  | 9, 0 => Some (mkAction 3 DR (Some 2))
  | 9, 1 => Some (mkAction 3 DL (Some 9))
  | 9, 2 => Some (mkAction 3 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | 10, 0 => Some (mkAction 0 DL (Some 5))
  | 10, 1 => Some (mkAction 0 DL (Some 10))
  | 10, 2 => Some (mkAction 0 DL (Some 10))
  | 10, 3 => Some (mkAction 0 DL (Some 10))
  | 11, 0 => Some (mkAction 0 DL (Some 10))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  | 12, 0 => Some (mkAction 1 DR (None))
  | 12, 1 => Some (mkAction 2 DL (Some 8))
  | 12, 2 => Some (mkAction 3 DL (Some 14))
  | 12, 3 => Some (mkAction 3 DL (Some 13))
  | 13, 0 => Some (mkAction 0 DL (Some 11))
  | 13, 1 => Some (mkAction 2 DL (Some 13))
  | 13, 2 => Some (mkAction 2 DL (Some 13))
  | 13, 3 => Some (mkAction 2 DL (Some 13))
  | 14, 0 => Some (mkAction 0 DL (Some 13))
  | 14, 1 => Some (mkAction 3 DL (Some 14))
  | 14, 2 => Some (mkAction 3 DL (Some 14))
  | 14, 3 => Some (mkAction 3 DL (Some 14))
  | _, _ => None
  end.

Lemma bb154_valid : ValidTM 15 4 bb154.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|sym]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|sym]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb154_core : Fwp2_4Core bb154. Proof. constructor; reflexivity. Qed.
Lemma bb154_ijk : Fwp2_4_IJKCore bb154. Proof. constructor; [exact bb154_core | ..]; reflexivity. Qed.
Lemma bb154_l : Fwp2_4_LCore bb154. Proof. constructor; [exact bb154_ijk | ..]; reflexivity. Qed.
Lemma bb154_mn : Fwp2_4_MNCore bb154. Proof. constructor; [exact bb154_l | ..]; reflexivity. Qed.
Lemma bb154_o : Fwp2_4_OCore bb154. Proof. constructor; [exact bb154_mn | ..]; reflexivity. Qed.

Lemma bb154_init :
  Reaches bb154 initConfig (mkCfgR (Some 6) [] (rep 2 3 (0 :: 0 :: 0 :: 3 :: rep 3 2 []))) 17.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb154_halt : forall m, 3 <= m ->
  exists t, HaltsIn bb154 (mkCfgR (Some 6) [] (rep m 3 [0; 3])) t /\ m < t.
Proof.
  intros m Hm.
  destruct (f4_rule_G3_rep bb154 bb154_core m [0; 3] ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
  assert (H2 : Reaches bb154 (F4cfg (m - 1) a b [0; 3])
                             (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3]) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb154 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3])
                             (mkCfgR (Some 12) (3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []) 1).
  { apply steps_one. reflexivity. }
  assert (H4 : Reaches bb154 (mkCfgR (Some 12) (3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [])
                             (mkCfgR None (1 :: 3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []) 1).
  { apply steps_one. reflexivity. }
  exists (t1 + 1 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4].
  - specialize (Hge1 ltac:(lia)).
    pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)).
    pose proof (fgh_ge_self _ f_omega2_props (m - 1)). lia.
Qed.

Theorem BB15_4_champion :
  ValidTM 15 4 bb154 /\
  exists t, HaltsIn bb154 initConfig t /\ fPlus f_omega2 5 3 < t.
Proof.
  split; [exact bb154_valid |].
  pose proof bb154_init as H0.
  destruct (ijk_zero_step bb154 bb154_ijk 2 (0 :: 3 :: rep 3 2 []) ltac:(lia) ltac:(discriminate))
    as [m0 [t0 [H1 [_ [Hge0 _]]]]].
  destruct (ijk_zero_step bb154 bb154_ijk m0 (3 :: rep 3 2 []) ltac:(lia) ltac:(discriminate))
    as [m1 [t1 [H2 [Hm1 [Hge1 _]]]]].
  destruct (o_four_rep bb154 bb154_o 3 m1 [] Hge1) as [m2 [t2 [H3 [Hm2 Hge2]]]].
  destruct (bb154_halt m2 Hge2) as [t3 [H4 Ht3]].
  destruct H4 as [cf [H4 Hcf]].
  exists (17 + t0 + t1 + t2 + t3). split.
  - unfold HaltsIn. exists cf. split; [| exact Hcf].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4].
  - assert (HfPlus_S : forall g k n, fPlus g (S k) n = iter (fPlus g k) n n) by reflexivity.
    assert (Hm1_3 : 3 <= m1 - 1).
    { specialize (Hm1 Hge0). pose proof (fgh_gt_pos _ f_omega2_props (m0 - 1) ltac:(lia)). lia. }
    assert (Hle : iter (fPlus f_omega2 4) 3 3 <= iter (fPlus f_omega2 4) 3 (m1 - 1))
      by (apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | exact Hm1_3]).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB15_4_champion.
