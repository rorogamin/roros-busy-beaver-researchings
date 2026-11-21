From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwpw_8 Fwpw_8_Ladder Fwpw_8_Peeker.
Import ListNotations.

Definition bb16_9 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 4 DL (Some 6))
  | 0, 1 => Some (mkAction 5 DR (Some 0))
  | 0, 2 => Some (mkAction 3 DL (Some 12))
  | 0, 3 => Some (mkAction 6 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DR (Some 5))
  | 0, 5 => Some (mkAction 7 DR (Some 2))
  | 0, 6 => Some (mkAction 0 DR (Some 15))
  | 0, 7 => Some (mkAction 7 DR (Some 0))
  | 0, 8 => Some (mkAction 8 DR (Some 5))
  | 1, 0 => Some (mkAction 7 DR (Some 0))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 7))
  | 1, 4 => Some (mkAction 4 DL (Some 5))
  | 1, 5 => Some (mkAction 0 DL (Some 2))
  | 1, 6 => Some (mkAction 2 DL (Some 3))
  | 1, 7 => Some (mkAction 7 DL (Some 1))
  | 1, 8 => Some (mkAction 0 DR (Some 6))
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 2))
  | 2, 6 => Some (mkAction 3 DL (Some 2))
  | 2, 7 => Some (mkAction 1 DL (Some 1))
  | 2, 8 => Some (mkAction 5 DR (Some 12))
  | 3, 0 => Some (mkAction 7 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 4 DL (Some 3))
  | 3, 5 => Some (mkAction 1 DL (Some 3))
  | 3, 6 => Some (mkAction 3 DL (Some 3))
  | 3, 7 => Some (mkAction 3 DL (Some 1))
  | 3, 8 => Some (mkAction 8 DR (Some 1))
  | 4, 0 => Some (mkAction 3 DR (Some 1))
  | 4, 1 => Some (mkAction 7 DR (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 8))
  | 4, 3 => Some (mkAction 4 DR (Some 5))
  | 4, 6 => Some (mkAction 8 DR (Some 0))
  | 4, 7 => Some (mkAction 7 DR (Some 4))
  | 4, 8 => Some (mkAction 1 DL (Some 4))
  | 5, 0 => Some (mkAction 1 DL (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 5))
  | 5, 2 => Some (mkAction 3 DL (Some 1))
  | 5, 3 => Some (mkAction 6 DR (Some 5))
  | 5, 4 => Some (mkAction 4 DL (Some 1))
  | 5, 5 => Some (mkAction 1 DL (Some 5))
  | 5, 6 => Some (mkAction 3 DL (Some 5))
  | 5, 7 => Some (mkAction 3 DL (Some 4))
  | 5, 8 => Some (mkAction 0 DL (Some 10))
  | 6, 0 => Some (mkAction 3 DR (Some 1))
  | 6, 1 => Some (mkAction 1 DL (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 6))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 5 DL (Some 0))
  | 6, 7 => Some (mkAction 2 DR (Some 6))
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
  | 8, 7 => Some (mkAction 2 DR (Some 11))
  | 9, 0 => Some (mkAction 0 DR (Some 2))
  | 9, 2 => Some (mkAction 2 DL (Some 9))
  | 9, 3 => Some (mkAction 2 DL (Some 9))
  | 9, 7 => Some (mkAction 7 DL (Some 9))
  | 9, 8 => Some (mkAction 7 DL (Some 12))
  | 10, 0 => Some (mkAction 3 DR (Some 10))
  | 10, 1 => Some (mkAction 4 DR (Some 13))
  | 10, 2 => Some (mkAction 5 DL (Some 10))
  | 10, 3 => Some (mkAction 5 DL (Some 10))
  | 10, 5 => Some (mkAction 2 DR (Some 7))
  | 10, 6 => Some (mkAction 8 DR (Some 14))
  | 10, 7 => Some (mkAction 6 DL (Some 4))
  | 11, 0 => Some (mkAction 3 DR (Some 11))
  | 11, 1 => Some (mkAction 0 DL (Some 12))
  | 11, 2 => Some (mkAction 6 DL (Some 11))
  | 11, 3 => Some (mkAction 6 DL (Some 11))
  | 11, 6 => Some (mkAction 2 DR (Some 7))
  | 11, 7 => Some (mkAction 3 DL (Some 3))
  | 12, 0 => Some (mkAction 1 DR (None))
  | 12, 1 => Some (mkAction 3 DR (Some 0))
  | 12, 2 => Some (mkAction 5 DL (Some 15))
  | 12, 3 => Some (mkAction 1 DR (Some 10))
  | 12, 5 => Some (mkAction 6 DL (Some 14))
  | 12, 6 => Some (mkAction 7 DL (Some 13))
  | 12, 7 => Some (mkAction 6 DL (Some 11))
  | 12, 8 => Some (mkAction 5 DR (Some 14))
  | 13, 0 => Some (mkAction 3 DR (Some 13))
  | 13, 1 => Some (mkAction 6 DR (Some 1))
  | 13, 2 => Some (mkAction 7 DL (Some 13))
  | 13, 3 => Some (mkAction 7 DL (Some 13))
  | 13, 4 => Some (mkAction 6 DR (Some 0))
  | 13, 5 => Some (mkAction 8 DL (Some 13))
  | 13, 6 => Some (mkAction 2 DR (Some 14))
  | 13, 7 => Some (mkAction 2 DR (Some 7))
  | 13, 8 => Some (mkAction 2 DL (Some 12))
  | 14, 0 => Some (mkAction 3 DR (Some 13))
  | 14, 2 => Some (mkAction 6 DL (Some 14))
  | 14, 3 => Some (mkAction 6 DL (Some 14))
  | 14, 4 => Some (mkAction 8 DR (Some 5))
  | 14, 5 => Some (mkAction 2 DR (Some 15))
  | 14, 6 => Some (mkAction 2 DR (Some 12))
  | 15, 0 => Some (mkAction 3 DR (Some 14))
  | 15, 2 => Some (mkAction 5 DL (Some 15))
  | 15, 3 => Some (mkAction 5 DL (Some 15))
  | 15, 5 => Some (mkAction 2 DR (Some 12))
  | 15, 6 => Some (mkAction 0 DR (Some 8))
  | 15, 8 => Some (mkAction 8 DR (Some 2))
  | _, _ => None
  end.

Lemma bb16_9_valid : ValidTM 16 9 bb16_9.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb16_9_core : Fwpw_8Core bb16_9. Proof. constructor; reflexivity. Qed.
Lemma bb16_9_i : Fwpw_8_ICore bb16_9. Proof. constructor; [exact bb16_9_core | ..]; reflexivity. Qed.
Lemma bb16_9_j : Fwpw_8_JCore bb16_9. Proof. constructor; [exact bb16_9_i | ..]; reflexivity. Qed.
Lemma bb16_9_k : Fwpw_8_KCore bb16_9. Proof. constructor; [exact bb16_9_j | ..]; reflexivity. Qed.
Lemma bb16_9_pn : Fwpw_8_PeekerNCore bb16_9. Proof. constructor; [exact bb16_9_k | ..]; reflexivity. Qed.
Lemma bb16_9_po : Fwpw_8_PeekerOCore bb16_9. Proof. constructor; [exact bb16_9_pn | ..]; reflexivity. Qed.
Lemma bb16_9_pp : Fwpw_8_PeekerPCore bb16_9. Proof. constructor; [exact bb16_9_po | ..]; reflexivity. Qed.

Lemma bb16_9_init :
  Reaches bb16_9 initConfig (H8cfg 1 1 (7 :: 7 :: 7 :: 6 :: rep 8 5 (5 :: rep 10 2 []))) 300.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Theorem BB16_9_champion :
  ValidTM 16 9 bb16_9 /\
  exists t, HaltsIn bb16_9 initConfig t /\ f_omega_omega_plus 7 10 < t.
Proof.
  split; [exact bb16_9_valid |].
  pose proof bb16_9_init as H0.
  destruct (w8_peeker_77_odd bb16_9 bb16_9_pn 1 (7 :: 6 :: rep 8 5 (5 :: rep 10 2 [])) ltac:(lia)) as [n1 [t1 [H1 [Hinc1 [_ [_ Ho1]]]]]].
  destruct (w8_peeker_6_odd bb16_9 bb16_9_pn n1 (rep 8 5 (5 :: rep 10 2 [])) ltac:(lia) Ho1) as [n2 [t2 [H2 [Hinc2 [_ [_ Ho2]]]]]].
  destruct (StepF7Odd_rep bb16_9 5 (f_omega_omega_plus 5) (fPlus_props _ f_omega_omega_props 5) (w8_peeker_5_odd bb16_9 bb16_9_po) 8 n2 (5 :: rep 10 2 []) ltac:(lia) Ho2) as [n3 [t3 [H3 [Hinc3 [_ [_ Ho3]]]]]].
  destruct (w8_peeker_5_odd bb16_9 bb16_9_po n3 (rep 10 2 []) ltac:(lia) Ho3) as [n4 [t4 [H4 [Hinc4 [Hf4 [_ Ho4]]]]]].
  destruct (StepF7Odd_rep bb16_9 2 (f_omega_omega_plus 6) (fPlus_props _ f_omega_omega_props 6) (w8_peeker_2_odd bb16_9 bb16_9_pp) 10 n4 [] ltac:(lia) Ho4) as [n5 [t5 [H5 [Hinc5 [Hf5 [Ht5 _]]]]]].
  assert (Hhalt1 : Reaches bb16_9 (H8cfg n5 1 [7]) (mkCfgR (Some 12) (2 :: 2 :: rep n5 3 []) []) 1) by (unfold H8cfg; apply steps_one; reflexivity).
  assert (Hhalt2 : Reaches bb16_9 (mkCfgR (Some 12) (2 :: 2 :: rep n5 3 []) []) (mkCfgR None (1 :: 2 :: 2 :: rep n5 3 []) []) 1) by (apply steps_one; reflexivity).
  exists (300 + t1 + t2 + t3 + t4 + t5 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 2 :: 2 :: rep n5 3 []) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4] | exact H5] | exact Hhalt1] | exact Hhalt2].
  - assert (HfPlus_S : forall k n, f_omega_omega_plus (S k) n = iter (f_omega_omega_plus k) n n) by reflexivity.
    pose proof (Hf4 3 ltac:(lia) ltac:(lia)) as Hbase4.
    assert (Hle_gen : forall n, 1 <= n -> f_omega_omega n <= f_omega_omega_plus 5 n)
      by (intros n Hn; unfold f_omega_omega_plus; apply (fPlus_mono_idx f_omega_omega f_omega_omega_props 0 5 n Hn ltac:(lia))).
    pose proof (Hle_gen 3 ltac:(lia)) as Hle3.
    pose proof f_omega_omega_3_ge_40 as H40.
    pose proof (Hf5 10 ltac:(lia) ltac:(lia)) as Hfinal.
    specialize (Ht5 ltac:(lia)).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB16_9_champion.
