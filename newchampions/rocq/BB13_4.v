From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2_4 Fwp2_4_Ladder.
Import ListNotations.

(* BB(13,4) champion (fwp23fw_4):
   1LD2RG2LA3LG_3LM2LH2RB2RF_1LG1RC2RB3LG_0RC1RC1LD3RD_3RD1LE1LE3LE_1RI3LD2LE3LE_1RG1LH2RG3LG_1RC2LH1LA1LE_0LJ0LK1LL1RZ_3RC3LJ3LJ3LJ_0LF0LK0LK0LK_0LK1LL1LL1LL_0LL2LM2LM---
   Proves: ValidTM 13 4 bb134 /\ exists t, HaltsIn bb134 initConfig t /\ fPlus f_omega2 3 14 < t.
   (Note: f_omega 2 = 8 < 14, so f_{ω^2+3}(14) > f_{ω^2+3}(f_ω(2)).) *)

Definition bb134 : TM := fun s sym =>
  match s, sym with
  (* A (0): 1LD 2RG 2LA 3LG *)
  | 0, 0 => Some (mkAction 1 DL (Some 3))
  | 0, 1 => Some (mkAction 2 DR (Some 6))
  | 0, 2 => Some (mkAction 2 DL (Some 0))
  | 0, 3 => Some (mkAction 3 DL (Some 6))
  (* B (1): 3LM 2LH 2RB 2RF *)
  | 1, 0 => Some (mkAction 3 DL (Some 12))
  | 1, 1 => Some (mkAction 2 DL (Some 7))
  | 1, 2 => Some (mkAction 2 DR (Some 1))
  | 1, 3 => Some (mkAction 2 DR (Some 5))
  (* C (2): 1LG 1RC 2RB 3LG *)
  | 2, 0 => Some (mkAction 1 DL (Some 6))
  | 2, 1 => Some (mkAction 1 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 1))
  | 2, 3 => Some (mkAction 3 DL (Some 6))
  (* D (3): 0RC 1RC 1LD 3RD *)
  | 3, 0 => Some (mkAction 0 DR (Some 2))
  | 3, 1 => Some (mkAction 1 DR (Some 2))
  | 3, 2 => Some (mkAction 1 DL (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  (* E (4): 3RD 1LE 1LE 3LE *)
  | 4, 0 => Some (mkAction 3 DR (Some 3))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  (* F (5): 1RI 3LD 2LE 3LE *)
  | 5, 0 => Some (mkAction 1 DR (Some 8))
  | 5, 1 => Some (mkAction 3 DL (Some 3))
  | 5, 2 => Some (mkAction 2 DL (Some 4))
  | 5, 3 => Some (mkAction 3 DL (Some 4))
  (* G (6): 1RG 1LH 2RG 3LG *)
  | 6, 0 => Some (mkAction 1 DR (Some 6))
  | 6, 1 => Some (mkAction 1 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DR (Some 6))
  | 6, 3 => Some (mkAction 3 DL (Some 6))
  (* H (7): 1RC 2LH 1LA 1LE *)
  | 7, 0 => Some (mkAction 1 DR (Some 2))
  | 7, 1 => Some (mkAction 2 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 0))
  | 7, 3 => Some (mkAction 1 DL (Some 4))
  (* I (8): 0LJ 0LK 1LL 1RZ *)
  | 8, 0 => Some (mkAction 0 DL (Some 9))
  | 8, 1 => Some (mkAction 0 DL (Some 10))
  | 8, 2 => Some (mkAction 1 DL (Some 11))
  | 8, 3 => Some (mkAction 1 DR None)
  (* J (9): 3RC 3LJ 3LJ 3LJ *)
  | 9, 0 => Some (mkAction 3 DR (Some 2))
  | 9, 1 => Some (mkAction 3 DL (Some 9))
  | 9, 2 => Some (mkAction 3 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  (* K (10): 0LF 0LK 0LK 0LK *)
  | 10, 0 => Some (mkAction 0 DL (Some 5))
  | 10, 1 => Some (mkAction 0 DL (Some 10))
  | 10, 2 => Some (mkAction 0 DL (Some 10))
  | 10, 3 => Some (mkAction 0 DL (Some 10))
  (* L (11): 0LK 1LL 1LL 1LL *)
  | 11, 0 => Some (mkAction 0 DL (Some 10))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | 11, 3 => Some (mkAction 1 DL (Some 11))
  (* M (12): 0LL 2LM 2LM --- *)
  | 12, 0 => Some (mkAction 0 DL (Some 11))
  | 12, 1 => Some (mkAction 2 DL (Some 12))
  | 12, 2 => Some (mkAction 2 DL (Some 12))
  | _, _ => None
  end.

Lemma bb134_valid : ValidTM 13 4 bb134.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|sym]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|sym]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb134_core : Fwp2_4Core bb134.
Proof. constructor; reflexivity. Qed.

Lemma bb134_ijk : Fwp2_4_IJKCore bb134.
Proof. constructor; [exact bb134_core | ..]; reflexivity. Qed.

Lemma bb134_l : Fwp2_4_LCore bb134.
Proof. constructor; [exact bb134_ijk | ..]; reflexivity. Qed.

Lemma bb134_init :
  Reaches bb134 initConfig (mkCfgR (Some 6) [] (rep 2 3 (0 :: 0 :: 0 :: rep 15 2 [3]))) 301.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb134_halt : forall m, 3 <= m ->
  exists t, HaltsIn bb134 (mkCfgR (Some 6) [] (rep m 3 [0; 3])) t /\ m < t.
Proof.
  intros m Hm.
  destruct (f4_rule_G3_rep bb134 bb134_core m [0; 3] ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
  assert (H2 : Reaches bb134 (F4cfg (m - 1) a b [0; 3])
                             (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3]) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb134 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [3])
                             (mkCfgR None (1 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []) 1).
  { apply steps_one. reflexivity. }
  exists (t1 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  - specialize (Hge1 ltac:(lia)).
    pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)).
    pose proof (fgh_ge_self _ f_omega2_props (m - 1)). lia.
Qed.

Theorem BB13_4_champion :
  ValidTM 13 4 bb134 /\
  exists t, HaltsIn bb134 initConfig t /\ fPlus f_omega2 3 14 < t.
Proof.
  split; [exact bb134_valid |].
  pose proof bb134_init as H0.
  destruct (ijk_zero_step bb134 bb134_ijk 2 (0 :: rep 15 2 [3]) ltac:(lia) ltac:(discriminate))
    as [m0 [t0 [H1 [_ [Hge0 _]]]]].
  destruct (ijk_zero_step bb134 bb134_ijk m0 (rep 15 2 [3]) ltac:(lia) ltac:(discriminate))
    as [m1 [t1 [H2 [Hm1 [Hge1 _]]]]].
  destruct (l_two_rep bb134 bb134_l 15 m1 [3] Hge1 ltac:(discriminate))
    as [m2 [t2 [H3 [Hm2 Hge2]]]].
  destruct (bb134_halt m2 Hge2) as [t3 [H4 Ht3]].
  destruct H4 as [cf [H4 Hcf]].
  exists (301 + t0 + t1 + t2 + t3). split.
  - unfold HaltsIn. exists cf. split; [| exact Hcf].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3] | exact H4].
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
    assert (H14 : 14 <= f_omega2 2).
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
    assert (Hm1_14 : 14 <= m1 - 1).
    { specialize (Hm1 Hge0).
      pose proof (fgh_mono _ f_omega2_props 2 (m0 - 1) ltac:(lia)). lia. }
    assert (H15 : iter (fPlus f_omega2 2) 14 14 <= iter (fPlus f_omega2 2) 15 (m1 - 1)).
    { eapply Nat.le_trans.
      - apply (iter_mono_steps _ (fgh_ge_self _ (fPlus_props _ f_omega2_props 2)) 14 15 14 ltac:(lia)).
      - apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props | exact Hm1_14]. }
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB13_4_champion.
