(*
  rocq/Fwp2_7.v
  Shared 7-state fwp21_7 reload (sym = 2) and halt ([5]) layer on top of Fwp2Core.
  Powers BB(7, 7), BB(7, 8), and BB(7, 9).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2.
Import ListNotations.

Record Fwp2_7Core (tm : TM) : Prop := mkFwp2_7Core {
  f7_fp : Fwp2Core tm;
  f7_A2 : tm 0 2 = Some (mkAction 6 DL (Some 0));
  f7_A5 : tm 0 5 = Some (mkAction 5 DR (Some 2));
  f7_A6 : tm 0 6 = Some (mkAction 5 DL (Some 0));
  f7_B0 : tm 1 0 = Some (mkAction 1 DR None);
  f7_B6 : tm 1 6 = Some (mkAction 6 DL (Some 3));
  f7_C6 : tm 2 6 = Some (mkAction 5 DR (Some 1));
  f7_D6 : tm 3 6 = Some (mkAction 1 DL (Some 0))
}.

Definition H2_7 (m : nat) : nat := Pempty (2 * m + 1).

Lemma H2_7_mono : forall x y, x <= y -> H2_7 x <= H2_7 y.
Proof. intros x y Hxy. unfold H2_7. apply Pempty_mono; lia. Qed.

Lemma H2_7_0_ge : 17 <= H2_7 0.
Proof.
  assert (Hiter2 : forall g : nat -> nat, iter g 2 0 = g (g 0)) by reflexivity.
  assert (H1 : Pfn 1 1 0 = Pfn 1 0 (Pfn 1 0 0)) by apply Hiter2.
  pose proof (Pfn_ge_succ 1 0 (Pfn 1 0 0)) as H2.
  assert (H0 : Pfn 1 0 0 = 15) by reflexivity.
  assert (H3 : 16 <= Pfn 1 1 0) by lia.
  unfold H2_7, Pempty; change (17 <= S (Pfn 1 1 0)); lia.
Qed.

Lemma H2_7_inc : forall m, 1 <= m -> S m <= H2_7 m.
Proof. intros m _. unfold H2_7. pose proof (Pempty_ge (2 * m + 1)). lia. Qed.

Lemma H2_7_gt : forall m, 1 <= m -> f_omega2 m < H2_7 m.
Proof.
  intros m _. unfold H2_7.
  pose proof (Pempty_gt_f_omega2 m).
  pose proof (Pempty_mono m (2 * m + 1) ltac:(lia)). lia.
Qed.

Section Fwp2_7Lemmas.
  Variable tm : TM.
  Hypothesis h7 : Fwp2_7Core tm.

  Local Lemma loop_B5_7 : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 5 R)) (mkCfgR (Some 1) (rep n 5 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 4 _ L 5 _ (fp_B5 _ (f7_fp _ h7))) |].
    specialize (IH (5 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_A_3to5 : forall n L R,
    Reaches tm (mkCfgR (Some 0) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 0) L (2 :: rep n 5 R)) (3 * n).
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    replace (3 * S k) with (S (S (S (3 * k)))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 3 2 _ _ R (f7_A2 _ h7)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (6 :: R) (kc_A3 _ _ (fp_kc _ (f7_fp _ h7)))) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 4 2 6 _ _ R (f7_A6 _ h7)) |].
    specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma rep_app_5 : forall a b L, rep a 5 (rep b 5 L) = rep (a + b) 5 L.
  Proof. induction a as [| p IH]; intros b L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Theorem reload_2_7 : forall r m R,
    exists t, Reaches tm (Scfg (S r) 0 m (2 :: R))
                         (mkCfgR (Some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) t.
  Proof.
    intros r m R. eexists. eapply reaches_trans.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 2 _ _ R (f7_A2 _ h7)) |].
      eapply reaches_trans; [apply (loop_A_3to5 (2 * m + 1) (rep (S r) 5 []) (6 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 5 2 _ _ _ (f7_A2 _ h7)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ (f7_A5 _ h7)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 4 _ _ 6 _ (f7_C6 _ h7)) |].
      pose proof (loop_B5_7 (2 * m + 1) (5 :: 5 :: rep r 5 []) (6 :: R)) as HB.
      change (5 :: 5 :: rep r 5 []) with (rep (S (S r)) 5 []) in HB.
      rewrite rep_app_5 in HB. exact HB.
    - replace (2 * m + 1 + S (S r)) with (S (r + 2 * m + 2)) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 5 5 6 _ _ R (f7_B6 _ h7)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 (6 :: R) (fp_D5 _ (f7_fp _ h7))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 0 3 6 _ _ R (f7_D6 _ h7)) |].
      apply steps_one. apply (step_mkCfgR_R _ 0 1 _ _ 3 (1 :: R) (kc_A3 _ _ (fp_kc _ (f7_fp _ h7)))).
  Qed.

  Theorem rule_2_7 : forall r m R,
    exists r' m' t, Reaches tm (Scfg (S r) 0 m (2 :: R)) (Scfg (S r') 0 m' R) t /\
      H2_7 m <= m' /\ m' <= t.
  Proof.
    intros r m R.
    destruct (reload_2_7 r m R) as [t1 H1].
    replace (r + 2 * m + 2) with (S (r + 2 * m + 1)) in H1 by lia.
    destruct (fwp2_empty3 tm (f7_fp _ h7) (r + 2 * m + 1) R) as [t2 [H2s Hle2]].
    exists (r + 2 * m + 1), (Pempty (r + 2 * m + 1)), (t1 + t2).
    split; [eapply reaches_trans; eassumption | split; [unfold H2_7; apply Pempty_mono; lia | lia]].
  Qed.

  Theorem rule_2_7_rep : forall n r m R,
    exists r' m' t, Reaches tm (Scfg (S r) 0 m (rep n 2 R)) (Scfg (S r') 0 m' R) t /\
      iter H2_7 n m <= m' /\ (1 <= n -> m' <= t).
  Proof.
    induction n as [| p IH]; intros r m R.
    - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
    - destruct p as [| p'].
      + destruct (rule_2_7 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
        exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
      + destruct (rule_2_7 r m (rep (S p') 2 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
        destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
        exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
        * replace (iter H2_7 (S (S p')) m) with (iter H2_7 (S p') (H2_7 m))
            by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
          eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_7_mono | exact Hm1] | exact Hm2].
        * intros _. pose proof (Ht2 ltac:(lia)). lia.
  Qed.

  Theorem rule_halt_5_7 : forall r m,
    exists cf, Reaches tm (Scfg (S r) 0 m [5]) cf 3 /\ cfg_st cf = None.
  Proof.
    intros r m. eexists. split.
    - eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 [] (f7_A5 _ h7)) |].
      eapply steps_succ; [apply (step_mkCfgR_R_nil _ 2 2 _ _ (kc_C0 _ _ (fp_kc _ (f7_fp _ h7)))) |].
      apply steps_one. apply (step_mkCfgR_R_nil _ 1 0 _ _ (f7_B0 _ h7)).
    - reflexivity.
  Qed.

End Fwp2_7Lemmas.
