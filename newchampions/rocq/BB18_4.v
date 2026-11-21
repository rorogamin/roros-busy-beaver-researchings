From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2_4 Fwp2_4_Ladder.
Import ListNotations.

Definition bb184 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 1 DL (Some 3))
  | 0, 1 => Some (mkAction 2 DR (Some 6))
  | 0, 2 => Some (mkAction 2 DL (Some 0))
  | 0, 3 => Some (mkAction 3 DL (Some 6))
  | 1, 0 => Some (mkAction 1 DR (Some 16))
  | 1, 1 => Some (mkAction 2 DL (Some 7))
  | 1, 2 => Some (mkAction 2 DR (Some 1))
  | 1, 3 => Some (mkAction 2 DR (Some 5))
  | 2, 0 => Some (mkAction 2 DL (Some 4))
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
  | 12, 1 => Some (mkAction 2 DL (Some 15))
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
  | 15, 0 => Some (mkAction 3 DL (Some 14))
  | 15, 1 => Some (mkAction 2 DL (Some 15))
  | 15, 2 => Some (mkAction 2 DL (Some 15))
  | 15, 3 => Some (mkAction 2 DL (Some 15))
  | 16, 0 => Some (mkAction 2 DR (Some 17))
  | 16, 1 => Some (mkAction 2 DR (Some 16))
  | 16, 2 => Some (mkAction 1 DL (Some 16))
  | 16, 3 => Some (mkAction 1 DL (Some 8))
  | 17, 0 => Some (mkAction 1 DL (Some 16))
  | 17, 3 => Some (mkAction 3 DL (Some 15))
  | _, _ => None
  end.

Lemma bb184_valid : ValidTM 18 4 bb184.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|sym]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|sym]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb184_core : Fwp2_4Core bb184. Proof. constructor; reflexivity. Qed.
Lemma bb184_ijk : Fwp2_4_IJKCore bb184. Proof. constructor; [exact bb184_core | ..]; reflexivity. Qed.
Lemma bb184_l : Fwp2_4_LCore bb184. Proof. constructor; [exact bb184_ijk | ..]; reflexivity. Qed.
Lemma bb184_mn : Fwp2_4_MNCore bb184. Proof. constructor; [exact bb184_l | ..]; reflexivity. Qed.
Lemma bb184_o : Fwp2_4_OCore bb184. Proof. constructor; [exact bb184_mn | ..]; reflexivity. Qed.
Lemma bb184_p : Fwp2_4_PCore bb184. Proof. constructor; [exact bb184_o | ..]; reflexivity. Qed.

Lemma bb184_init :
  Reaches bb184 initConfig (mkCfgR (Some 6) [] (rep 2 3 (0 :: 0 :: 0 :: 0 :: 3 :: rep 3 2 (rep 39 1 [])))) 634.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb184_halt : forall m, 3 <= m ->
  exists t, HaltsIn bb184 (mkCfgR (Some 6) [] (rep m 3 [0; 3])) t /\ m < t.
Proof.
  intros m Hm.
  destruct (f4_rule_G3_rep bb184 bb184_core m [0; 3] ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
  assert (H2 : Reaches bb184 (F4cfg (m - 1) a b [0; 3])
                              (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3]) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb184 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3])
                              (mkCfgR (Some 12) (3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []) 1).
  { apply steps_one. reflexivity. }
  assert (H4 : Reaches bb184 (mkCfgR (Some 12) (3 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [])
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

Theorem BB18_4_champion :
  ValidTM 18 4 bb184 /\
  exists t, HaltsIn bb184 initConfig t /\ fPlus f_omega2 6 39 < t.
Proof.
  split; [exact bb184_valid |].
  pose proof bb184_init as H0.
  destruct (ijk_zero_step bb184 bb184_ijk 2 (0 :: 0 :: 3 :: rep 3 2 (rep 39 1 [])) ltac:(lia) ltac:(discriminate)) as [m0 [t0 [H1 [_ [Hge0 _]]]]].
  destruct (ijk_zero_step bb184 bb184_ijk m0 (0 :: 3 :: rep 3 2 (rep 39 1 [])) ltac:(lia) ltac:(discriminate)) as [m0' [t0' [H1' [Hm0' [Hge0' _]]]]].
  destruct (ijk_zero_step bb184 bb184_ijk m0' (3 :: rep 3 2 (rep 39 1 [])) ltac:(lia) ltac:(discriminate)) as [m1 [t1 [H2 [Hm1 [Hge1 _]]]]].
  destruct (o_four_rep bb184 bb184_o 3 m1 (rep 39 1 []) Hge1) as [m2 [t2 [H3 [Hm2 Hge2]]]].
  destruct (p_five_rep bb184 bb184_p 39 m2 [] Hge2) as [m3 [t3 [H4 [Hm3 Hge3]]]].
  destruct (bb184_halt m3 Hge3) as [t4 [H5 Ht4]].
  destruct H5 as [cf [H5 Hcf]].
  exists (634 + t0 + t0' + t1 + t2 + t3 + t4). split.
  - unfold HaltsIn. exists cf. split; [| exact Hcf].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H1'] | exact H2] | exact H3] | exact H4] | exact H5].
  - assert (HfPlus_S : forall g k n, fPlus g (S k) n = iter (fPlus g k) n n) by reflexivity.
    assert (Hf01 : forall n, fOmegaMul 0 1 n = 2 * n).
    { intro n. assert (Haux : forall j x, iter fZero j x = j + x).
      { induction j as [| j' IH]; intro x; [reflexivity | simpl; rewrite IH; unfold fZero; lia]. }
      change (iter fZero n n = 2 * n). rewrite Haux. lia. }
    assert (Hf10_ge : forall n, 1 <= n -> 2 * n <= fOmegaMul 1 0 n).
    { intros n Hn.
      assert (Hle : fOmegaMul 0 1 n <= fOmegaMul 0 n n)
        by (apply fPlus_mono_idx; [apply (fOmegaMul_props 0 0) | lia | lia]).
      rewrite Hf01 in Hle. exact Hle. }
    assert (Hf_w2_ge_2n : forall n, 2 <= n -> 2 * n <= f_omega2 n).
    { intros n Hn. rewrite f_omega2_eq.
      assert (Hle1 : fOmegaMul 1 0 n <= fOmegaMul n 0 n).
      { assert (Hma : forall a1 a2 x, a1 <= a2 -> fOmegaMul a1 0 x <= fOmegaMul a2 0 x).
        { intros a1 a2 x Ha. induction Ha as [| a2' Hle IH]; [lia |].
          eapply Nat.le_trans; [exact IH |].
          destruct x as [| x']; [change (fOmegaMul a2' 0 0 <= fOmegaMul a2' 0 0); lia |].
          change (fOmegaMul a2' 0 (S x') <= fOmegaMul a2' (S x') (S x')).
          apply fPlus_mono_idx; [apply (fOmegaMul_props a2' 0) | lia | lia]. }
        apply Hma; lia. }
      pose proof (Hf10_ge n ltac:(lia)). lia. }
    assert (H16 : 16 <= f_omega2 2).
    { assert (H10_2 : fOmegaMul 1 0 2 = 8) by reflexivity.
      assert (H11_2 : 16 <= fOmegaMul 1 1 2).
      { assert (Heq : forall x, fOmegaMul 1 1 x = iter (fOmegaMul 1 0) x x) by reflexivity.
        rewrite Heq, iter_succ, iter_succ, iter_zero, H10_2.
        pose proof (Hf10_ge 8 ltac:(lia)). lia. }
      assert (Hle : fOmegaMul 1 1 2 <= fOmegaMul 1 2 2)
        by (apply fPlus_mono_idx; [apply (fOmegaMul_props 1 0) | lia | lia]).
      rewrite f_omega2_eq.
      assert (Heq : forall k n, fOmegaMul (S k) 0 n = fOmegaMul k n n) by reflexivity.
      rewrite (Heq 1 2). lia. }
    assert (Hm0'_16 : 16 <= m0' - 1).
    { specialize (Hm0' Hge0). pose proof (fgh_mono _ f_omega2_props 2 (m0 - 1) ltac:(lia)). lia. }
    assert (Hm1_32 : 32 <= m1 - 1).
    { specialize (Hm1 Hge0'). pose proof (Hf_w2_ge_2n (m0' - 1) ltac:(lia)). lia. }
    assert (Hm2_39 : 39 <= m2 - 1).
    { pose proof (iter_ge_add_pos _ (fgh_gt_pos _ (fPlus_props _ f_omega2_props 4)) 3 (m1 - 1) ltac:(lia)).
      (* Wait: 32 + 3 = 35 < 39; use f_omega2 (m1 - 1) >= 2 * 32 = 64! *)
      assert (H1step : fPlus f_omega2 4 (m1 - 1) <= iter (fPlus f_omega2 4) 3 (m1 - 1)).
      { rewrite !iter_succ, iter_zero.
        pose proof (fgh_ge_self _ (fPlus_props _ f_omega2_props 4) (fPlus f_omega2 4 (m1 - 1))).
        pose proof (fgh_ge_self _ (fPlus_props _ f_omega2_props 4) (fPlus f_omega2 4 (fPlus f_omega2 4 (m1 - 1)))). lia. }
      assert (H04 : f_omega2 (m1 - 1) <= fPlus f_omega2 4 (m1 - 1))
        by (apply fPlus_mono_idx; [exact f_omega2_props | lia | lia]).
      pose proof (Hf_w2_ge_2n (m1 - 1) ltac:(lia)). lia. }
    assert (Hle : iter (fPlus f_omega2 5) 39 39 <= iter (fPlus f_omega2 5) 39 (m2 - 1))
      by (apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | exact Hm2_39]).
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB18_4_champion.
