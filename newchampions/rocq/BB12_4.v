From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2_4 Fwp2_4_Ladder.
Import ListNotations.

(* BB(12,4) champion (fwp22fw_4):
   1LD2RG2LA3LG_2LL2LH2RB2RF_1LG1RC2RB3LG_0RC1RC1LD3RD_3RD1LE1LE3LE_1RI3LD2LE3LE_1RG1LH2RG3LG_1RC2LH1LA1LE_0LJ0LK1RZ---_3RC3LJ3LJ3LJ_0LF0LK0LK0LK_0LK1LL1LL---
   Proves: ValidTM 12 4 bb124 /\ exists t, HaltsIn bb124 initConfig t /\ fPlus f_omega2 2 14 < t.
   (Note: f_omega 2 = 8 < 14, so f_{ω^2+2}(14) > f_{ω^2+2}(f_ω(2)).) *)

Definition bb124 : TM := fun s sym =>
  match s, sym with
  (* A (0): 1LD 2RG 2LA 3LG *)
  | 0, 0 => Some (mkAction 1 DL (Some 3))
  | 0, 1 => Some (mkAction 2 DR (Some 6))
  | 0, 2 => Some (mkAction 2 DL (Some 0))
  | 0, 3 => Some (mkAction 3 DL (Some 6))
  (* B (1): 2LL 2LH 2RB 2RF *)
  | 1, 0 => Some (mkAction 2 DL (Some 11))
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
  (* I (8): 0LJ 0LK 1RZ --- *)
  | 8, 0 => Some (mkAction 0 DL (Some 9))
  | 8, 1 => Some (mkAction 0 DL (Some 10))
  | 8, 2 => Some (mkAction 1 DR None)
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
  (* L (11): 0LK 1LL 1LL --- *)
  | 11, 0 => Some (mkAction 0 DL (Some 10))
  | 11, 1 => Some (mkAction 1 DL (Some 11))
  | 11, 2 => Some (mkAction 1 DL (Some 11))
  | _, _ => None
  end.

Lemma bb124_valid : ValidTM 12 4 bb124.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|sym]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]];
    try (destruct sym as [|[|[|[|sym]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb124_core : Fwp2_4Core bb124.
Proof. constructor; reflexivity. Qed.

Lemma bb124_ijk : Fwp2_4_IJKCore bb124.
Proof. constructor; [exact bb124_core | ..]; reflexivity. Qed.

Lemma bb124_init :
  Reaches bb124 initConfig (mkCfgR (Some 6) [] (rep 2 3 (0 :: 0 :: rep 15 1 [2]))) 300.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma bb124_halt : forall m, 3 <= m ->
  exists t, HaltsIn bb124 (mkCfgR (Some 6) [] (rep m 3 [0; 2])) t /\ m < t.
Proof.
  intros m Hm.
  destruct (f4_rule_G3_rep bb124 bb124_core m [0; 2] ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
  assert (H2 : Reaches bb124 (F4cfg (m - 1) a b [0; 2])
                             (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [2]) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb124 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [2])
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

Theorem BB12_4_champion :
  ValidTM 12 4 bb124 /\
  exists t, HaltsIn bb124 initConfig t /\ fPlus f_omega2 2 14 < t.
Proof.
  split; [exact bb124_valid |].
  pose proof bb124_init as H0.
  destruct (ijk_zero_step bb124 bb124_ijk 2 (rep 15 1 [2]) ltac:(lia) ltac:(discriminate))
    as [m1 [t1 [H1 [_ [Hge1 _]]]]].
  destruct (ijk_one_rep bb124 bb124_ijk 15 m1 [2] Hge1 ltac:(discriminate))
    as [m2 [t2 [H2 [Hm2 Hge2]]]].
  destruct (bb124_halt m2 Hge2) as [t3 [H3 Ht3]].
  destruct H3 as [cf [H3 Hcf]].
  exists (300 + t1 + t2 + t3). split.
  - unfold HaltsIn. exists cf. split; [| exact Hcf].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3].
  - (* Polymorphic unfolding: NEVER normalize concrete FGH terms! *)
    assert (HfPlus_S : forall g k n, fPlus g (S k) n = iter (fPlus g k) n n) by reflexivity.
    assert (Hf01 : forall n, fOmegaMul 0 1 n = 2 * n).
    { intro n. assert (Haux : forall j x, iter fZero j x = j + x).
      { induction j as [| j' IH]; intro x; [reflexivity | simpl; rewrite IH; unfold fZero; lia]. }
      change (iter fZero n n = 2 * n). rewrite Haux. lia. }
    assert (Hf10_ge : forall n, 1 <= n -> 2 * n <= fOmegaMul 1 0 n).
    { intros n Hn.
      assert (Hle : fOmegaMul 0 1 n <= fOmegaMul 0 n n)
        by (apply fPlus_mono_idx; [apply (fOmegaMul_props 0 0) | lia | lia]).
      rewrite Hf01 in Hle. exact Hle. }
    assert (Hbase : 14 <= fPlus f_omega2 1 (m1 - 1)).
    { assert (H2' : fPlus f_omega2 1 2 <= fPlus f_omega2 1 (m1 - 1))
        by (apply (fgh_mono _ (fPlus_props _ f_omega2_props 1)); lia).
      assert (H10_2 : fOmegaMul 1 0 2 = 8) by reflexivity.
      assert (H11_2 : 16 <= fOmegaMul 1 1 2).
      { assert (Heq : forall x, fOmegaMul 1 1 x = iter (fOmegaMul 1 0) x x) by reflexivity.
        rewrite Heq, iter_succ, iter_succ, iter_zero, H10_2.
        pose proof (Hf10_ge 8 ltac:(lia)). lia. }
      assert (H14 : 14 <= f_omega2 2).
      { assert (Hle : fOmegaMul 1 1 2 <= fOmegaMul 1 2 2)
          by (apply fPlus_mono_idx; [apply (fOmegaMul_props 1 0) | lia | lia]).
        rewrite f_omega2_eq.
        assert (Heq : forall k n, fOmegaMul (S k) 0 n = fOmegaMul k n n) by reflexivity.
        rewrite (Heq 1 2). lia. }
      pose proof (fNext_ge _ f_omega2_props 2 ltac:(lia)).
      assert (Heq : forall x, fPlus f_omega2 1 x = fNext f_omega2 x) by reflexivity.
      rewrite Heq in H2'. lia. }
    assert (H15 : iter (fPlus f_omega2 1) 14 14 <= iter (fPlus f_omega2 1) 15 (m1 - 1)).
    { replace 15 with (14 + 1) by lia. rewrite iter_add.
      apply iter_mono_arg; [apply fgh_mono, fPlus_props, f_omega2_props |].
      rewrite iter_succ, iter_zero. exact Hbase. }
    rewrite HfPlus_S. lia.
Qed.

Print Assumptions BB12_4_champion.
