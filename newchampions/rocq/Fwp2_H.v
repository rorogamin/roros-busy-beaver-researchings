(*
  rocq/Fwp2_H.v
  Shared 8-state Fwp2_H layer on top of Fwp2Core:
    - sweep_HG: common H -> G left-right sweep
    - rule_2_H, rule_2_H_rep: f_{ω^2} reload on symbol 2
    - bounce_G2_2s, exec_G2_2s: shared 23-step bounce + H_plus2 > f_{ω^2+1}
  Powers ALL BB(8..11, 7..9) and BB(9..11, 6) champions!
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2.
Import ListNotations.

Record Fwp2_HCore (tm : TM) : Prop := mkFwp2_HCore {
  fh_fp : Fwp2Core tm;
  fh_A2 : tm 0 2 = Some (mkAction 2 DL (Some 7));
  fh_E2 : tm 4 2 = Some (mkAction 4 DR (Some 6));
  fh_F4 : tm 5 4 = Some (mkAction 5 DL (Some 5));
  fh_F5 : tm 5 5 = Some (mkAction 5 DL (Some 5));
  fh_G1 : tm 6 1 = Some (mkAction 4 DR (Some 6));
  fh_G2 : tm 6 2 = Some (mkAction 1 DL (Some 1));
  fh_H2 : tm 7 2 = Some (mkAction 1 DL (Some 7));
  fh_H3 : tm 7 3 = Some (mkAction 1 DL (Some 7));
  fh_H5 : tm 7 5 = Some (mkAction 5 DR (Some 6))
}.

Definition H2_H (m : nat) : nat := Pempty (2 * m + 2).
Definition H_plus2 (m : nat) : nat := iter H2_H (2 * m - 1) 17.

Lemma H2_H_mono : forall x y, x <= y -> H2_H x <= H2_H y.
Proof. intros x y Hxy. unfold H2_H. apply Pempty_mono; lia. Qed.

Lemma H2_H_0_ge : 17 <= H2_H 0.
Proof.
  assert (Hgen : forall r, Pfn (S r) 1 0 = Pfn (S r) 0 (Pfn (S r) 0 0)) by reflexivity.
  pose proof (Hgen 0) as H1.
  pose proof (Pfn_ge_succ 1 0 (Pfn 1 0 0)) as H2.
  assert (H0 : Pfn 1 0 0 = 15) by reflexivity.
  assert (H17 : 17 <= Pempty 1) by (change (17 <= S (Pfn 1 1 0)); lia).
  unfold H2_H. pose proof (Pempty_mono 1 (2 * 0 + 2) ltac:(lia)). lia.
Qed.

Lemma H2_H_inc : forall m, 1 <= m -> S m <= H2_H m.
Proof. intros m _. unfold H2_H. pose proof (Pempty_ge (2 * m + 2)). lia. Qed.

Lemma H2_H_gt : forall m, 1 <= m -> f_omega2 m < H2_H m.
Proof.
  intros m _. unfold H2_H.
  pose proof (Pempty_gt_f_omega2 m).
  pose proof (Pempty_mono m (2 * m + 2) ltac:(lia)). lia.
Qed.

Lemma H_plus2_mono : forall x y, x <= y -> H_plus2 x <= H_plus2 y.
Proof.
  intros x y Hxy. unfold H_plus2.
  apply iter_mono_steps; [intro z; unfold H2_H; pose proof (Pempty_ge (2 * z + 2)); lia | lia].
Qed.

Lemma H_plus2_gt : forall m, 1 <= m -> f_omega2_plus 1 m < H_plus2 m.
Proof.
  intros m Hm. destruct m as [| m']; [lia |].
  unfold H_plus2.
  replace (2 * S m' - 1) with (S m' + m') by lia.
  rewrite iter_add.
  assert (Hbase : S m' <= iter H2_H m' 17).
  { pose proof (iter_ge_add_pos H2_H H2_H_inc m' 17 ltac:(lia)). lia. }
  pose proof (iter_mono_arg H2_H H2_H_mono (S m') (S m') _ Hbase) as Harg.
  pose proof (iter_strict_dom H2_H f_omega2 1 H2_H_gt (fOmega2_props 1 0 0) (S m') (S m') ltac:(lia) ltac:(lia)) as Hlt.
  change (f_omega2_plus 1 (S m')) with (iter f_omega2 (S m') (S m')). lia.
Qed.

Lemma H_plus2_inc : forall m, 1 <= m -> S m <= H_plus2 m.
Proof.
  intros m Hm. pose proof (H_plus2_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 1) m).
  change (f_omega2_plus 1 m) with (fOmega2 1 0 1 m) in *. lia.
Qed.

Lemma H_plus2_ge_17 : forall m, 17 <= H_plus2 m.
Proof.
  intro m. unfold H_plus2.
  apply iter_ge_self; intro z; unfold H2_H; pose proof (Pempty_ge (2 * z + 2)); lia.
Qed.

Lemma climb_2m_minus_1 :
  forall (H f : nat -> nat) (c : nat),
    1 <= c ->
    (forall x y, x <= y -> H x <= H y) ->
    (forall x, 1 <= x -> S x <= H x) ->
    (forall x, 1 <= x -> f x < H x) ->
    FGHProps f ->
    forall m, 1 <= m -> fNext f m < iter H (2 * m - 1) c.
Proof.
  intros H f c Hc Hmono Hinc Hdom Hf m Hm. destruct m as [| m']; [lia |].
  replace (2 * S m' - 1) with (S m' + m') by lia.
  rewrite iter_add.
  assert (Hbase : S m' <= iter H m' c) by (pose proof (iter_ge_add_pos H Hinc m' c Hc); lia).
  pose proof (iter_mono_arg H Hmono (S m') (S m') _ Hbase) as Harg.
  pose proof (iter_strict_dom H f 1 Hdom Hf (S m') (S m') ltac:(lia) ltac:(lia)) as Hlt.
  unfold fNext. lia.
Qed.

Section Fwp2_HLemmas.
  Variable tm : TM.
  Hypothesis hh : Fwp2_HCore tm.

  Lemma loop_H3 : forall n L R,
    Reaches tm (mkCfgR (Some 7) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 7) L (3 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 0 3 3 _ _ R (fh_H3 _ hh)) |].
    specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_G1 : forall n L R,
    Reaches tm (mkCfgR (Some 6) L (rep n 1 R))
               (mkCfgR (Some 6) (rep n 4 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 6 3 _ L 1 _ (fh_G1 _ hh)) |].
    specialize (IH (4 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_F4 : forall n L R,
    Reaches tm (mkCfgR (Some 5) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 5) L (4 :: rep n 5 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 4 4 4 _ _ R (fh_F4 _ hh)) |].
    specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_F5 : forall n L R,
    Reaches tm (mkCfgR (Some 5) (rep n 5 L) (5 :: R))
               (mkCfgR (Some 5) L (5 :: rep n 5 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 4 5 5 _ _ R (fh_F5 _ hh)) |].
    specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_B5_H : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 5 R))
               (mkCfgR (Some 1) (rep n 5 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 4 _ L 5 _ (fp_B5 _ (fh_fp _ hh))) |].
    specialize (IH (5 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma rep_add_H : forall a b s L, rep a s (rep b s L) = rep (a + b) s L.
  Proof. induction a as [| p IH]; intros b s L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Theorem sweep_HG : forall r m mark R,
    exists t, Reaches tm (mkCfgR (Some 7) (rep (2 * m + 1) 3 (rep (S r) 5 [])) (2 :: mark :: R))
                         (mkCfgR (Some 6) (rep (2 * m + 2) 4 (rep (S r) 5 [])) (mark :: R)) t.
  Proof.
    intros r m mark R. eexists.
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 0 3 2 _ _ _ (fh_H2 _ hh)) |].
    eapply reaches_trans; [apply (loop_H3 (2 * m) (rep (S r) 5 []) (1 :: mark :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 0 5 3 _ _ _ (fh_H3 _ hh)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 7 4 _ _ 5 _ (fh_H5 _ hh)) |].
    replace (1 :: 1 :: rep (2 * m) 1 (mark :: R)) with (rep (2 * m + 2) 1 (mark :: R))
      by (replace (2 * m + 2) with (S (S (2 * m))) by lia; reflexivity).
    apply (loop_G1 (2 * m + 2) (rep (S r) 5 []) (mark :: R)).
  Qed.

  Theorem reload_2_H : forall r m R,
    exists t, Reaches tm (Scfg (S r) 0 m (2 :: R))
                         (mkCfgR (Some 0) (2 :: rep (r + 2 * m + 3) 5 []) (1 :: R)) t.
  Proof.
    intros r m R. destruct (sweep_HG r m 2 R) as [ts Hs].
    eexists. eapply reaches_trans.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 2 _ _ R (fh_A2 _ hh)) |].
      eapply reaches_trans; [exact Hs |].
      replace (2 * m + 2) with (S (S (2 * m))) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 4 2 _ _ R (fh_G2 _ hh)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 4 4 _ _ _ (fp_B4 _ (fh_fp _ hh))) |].
      apply (loop_F4 (2 * m) (rep (S r) 5 []) (3 :: 1 :: R)).
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 4 5 4 _ _ _ (fh_F4 _ hh)) |].
      change (5 :: rep (2 * m) 5 (3 :: 1 :: R)) with (rep (S (2 * m)) 5 (3 :: 1 :: R)).
      eapply reaches_trans; [apply (loop_F5 r [] (rep (S (2 * m)) 5 (3 :: 1 :: R))) |].
      rewrite rep_add_H.
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 4 5 _ _ (fh_F5 _ hh)) |].
      change (5 :: rep (r + S (2 * m)) 5 (3 :: 1 :: R)) with (rep (S (r + S (2 * m))) 5 (3 :: 1 :: R)).
      eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ (fh_fp _ hh))) |].
      eapply reaches_trans; [apply (loop_B5_H (S (r + S (2 * m))) [5] (3 :: 1 :: R)) |].
      rewrite rep_snoc_one.
      change (5 :: rep (S (r + S (2 * m))) 5 []) with (rep (S (S (r + S (2 * m)))) 5 []).
      replace (S (S (r + S (2 * m)))) with (r + 2 * m + 3) by lia.
      apply steps_one. apply (step_mkCfgR_R _ 1 1 _ _ 3 (1 :: R) (kc_B3 _ _ (fp_kc _ (fh_fp _ hh)))).
  Qed.

  Theorem rule_2_H : forall r m R,
    exists r' m' t, Reaches tm (Scfg (S r) 0 m (2 :: R)) (Scfg (S (S r')) 0 m' R) t /\
      H2_H m <= m' /\ m' <= t.
  Proof.
    intros r m R.
    destruct (reload_2_H r m R) as [t1 H1].
    replace (r + 2 * m + 3) with (S (r + 2 * m + 2)) in H1 by lia.
    destruct (fwp2_empty3 tm (fh_fp _ hh) (r + 2 * m + 2) R) as [t2 [H2s Hle2]].
    exists (r + 2 * m + 1), (Pempty (r + 2 * m + 2)), (t1 + t2).
    replace (S (S (r + 2 * m + 1))) with (S (r + 2 * m + 2)) by lia.
    split; [eapply reaches_trans; eassumption | split; [unfold H2_H; apply Pempty_mono; lia | lia]].
  Qed.

  Theorem rule_2_H_rep : forall n r m R,
    exists r' m' t, Reaches tm (Scfg (S r) 0 m (rep n 2 R)) (Scfg (S r') 0 m' R) t /\
      iter H2_H n m <= m' /\ (1 <= n -> m' <= t /\ 1 <= r').
  Proof.
    induction n as [| p IH]; intros r m R.
    - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
    - destruct p as [| p'].
      + destruct (rule_2_H r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
        exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; split; [exact Ht1 | lia]]].
      + destruct (rule_2_H r m (rep (S p') 2 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
        destruct (IH (S r1) m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
        exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
        * replace (iter H2_H (S (S p')) m) with (iter H2_H (S p') (H2_H m))
            by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
          eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_H_mono | exact Hm1] | exact Hm2].
        * intros _. destruct (Ht2 ltac:(lia)) as [Ht2a Hr2a]. lia.
  Qed.

  Theorem bounce_G2_2s : forall r R',
    exists t, Reaches tm (mkCfgR (Some 6) (rep (S r) 5 []) (2 :: 2 :: 2 :: 2 :: R'))
                         (Scfg (S r) 0 1 (1 :: R')) t.
  Proof.
    intros r R'.
    assert (H0 : Reaches tm
      (mkCfgR (Some 6) (5 :: rep r 5 []) (2 :: 2 :: 2 :: 2 :: R'))
      (mkCfgR (Some 5) (rep r 5 []) (3 :: 1 :: 1 :: 3 :: 1 :: R')) 15).
    { eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 5 2 _ _ _ (fh_G2 _ hh)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 4 _ _ 5 _ (fp_B5 _ (fh_fp _ hh))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 3 2 _ _ _ (kc_B2 _ _ (fp_kc _ (fh_fp _ hh)))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 1 _ _ 3 _ (kc_D3 _ _ (fp_kc _ (fh_fp _ hh)))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 0 2 1 _ _ _ (kc_C1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 5 2 _ _ _ (kc_B2 _ _ (fp_kc _ (fh_fp _ hh)))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ (fp_D5 _ (fh_fp _ hh))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 1 _ (fp_D1 _ (fh_fp _ hh))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ _ 1 _ (fp_E1 _ (fh_fp _ hh))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 4 3 _ _ 2 _ (fh_E2 _ hh)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 4 2 _ _ _ (fh_G2 _ hh)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 3 4 _ _ _ (fp_B4 _ (fh_fp _ hh))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ _ (fp_F3 _ (fh_fp _ hh))) |].
      apply steps_one. apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ _ (fp_F3 _ (fh_fp _ hh))). }
    assert (Htail : exists tt, Reaches tm
      (mkCfgR (Some 5) (rep r 5 []) (3 :: 1 :: 1 :: 3 :: 1 :: R'))
      (Scfg (S r) 0 1 (1 :: R')) tt).
    { destruct r as [| r'].
      - exists 6.
        eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 0 3 _ _ (fp_F3 _ (fh_fp _ hh))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ (fh_fp _ hh))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 1 1 _ _ 3 _ (kc_B3 _ _ (fp_kc _ (fh_fp _ hh)))).
      - eexists.
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 5 3 _ _ _ (fp_F3 _ (fh_fp _ hh))) |].
        eapply reaches_trans; [apply (loop_F5 r' [] (1 :: 1 :: 1 :: 3 :: 1 :: R')) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 4 5 _ _ (fh_F5 _ hh)) |].
        change (5 :: rep r' 5 (1 :: 1 :: 1 :: 3 :: 1 :: R')) with (rep (S r') 5 (1 :: 1 :: 1 :: 3 :: 1 :: R')).
        eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ (fh_fp _ hh))) |].
        eapply reaches_trans; [apply (loop_B5_H (S r') [5] (1 :: 1 :: 1 :: 3 :: 1 :: R')) |].
        rewrite rep_snoc_one.
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ (fh_fp _ hh)))) |].
        apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 1 1 _ _ 3 _ (kc_B3 _ _ (fp_kc _ (fh_fp _ hh)))). }
    destruct Htail as [tt Ht].
    exists (15 + tt). eapply reaches_trans; [exact H0 | exact Ht].
  Qed.

  Theorem exec_G2_2s : forall r m R, 1 <= m ->
    exists r' m' t, Reaches tm (mkCfgR (Some 6) (rep (S r) 5 []) (rep (2 * m + 3) 2 R))
                               (Scfg (S (S r')) 0 m' R) t /\ H_plus2 m <= m' /\ m' <= t.
  Proof.
    intros r m R Hm. destruct m as [| m']; [lia |].
    replace (2 * S m' + 3) with (S (S (S (S (2 * m' + 1))))) by lia.
    destruct (bounce_G2_2s r (rep (2 * m' + 1) 2 R)) as [t0 H0].
    destruct (fwp2_step tm (fh_fp _ hh) (S r) 0 1 (rep (2 * m' + 1) 2 R)) as [t1 [H1 _]].
    assert (HM17 : 17 <= Pfn (S r) 0 1).
    { pose proof (Pfn_mono_r 1 (S r) 0 1 ltac:(lia)) as Hmr.
      assert (Hge : forall j M, S M <= PexitOf Kfn j M).
      { intro j. induction j as [| p IHp]; intro M; [simpl; lia |].
        change (S M <= PexitOf Kfn p (Kfn (S p) M)).
        pose proof (IHp (Kfn (S p) M)). pose proof (Kfn_ge_succ (S p) M). lia. }
      assert (Hp1 : S (Kfn 4 0) <= Pfn 1 0 1).
      { assert (Hpg : forall m, Pfn 1 0 m = PexitOf Kfn (2 * m + 2) 0) by reflexivity.
        assert (Hpeg : forall j M, PexitOf Kfn (S j) M = PexitOf Kfn j (Kfn (S j) M)) by reflexivity.
        rewrite Hpg. replace (2 * 1 + 2) with 4 by lia. rewrite Hpeg. apply Hge. }
      assert (HK1 : forall n, 2 * n <= iter (Kfn 1) n 0).
      { intro n. induction n as [| p IHp]; [simpl; lia |].
        rewrite iter_succ.
        assert (Hg : forall z, 2 * z + 2 <= Kfn 1 z).
        { intro z. change (2 * z + 2 <= iter (Kfn 0) (2 * z + 2) 0).
          assert (Hg0 : forall q, q <= iter (Kfn 0) q 0).
          { intro q. induction q as [| u IHu]; [simpl; lia | rewrite iter_succ; change (S u <= S (iter (Kfn 0) u 0)); lia]. }
          apply Hg0. }
        pose proof (Hg (iter (Kfn 1) p 0)). lia. }
      assert (HKgen : forall j, Kfn (S j) 0 = Kfn j (Kfn j 0)) by reflexivity.
      assert (HK20 : Kfn 2 0 = 6) by reflexivity.
      assert (HK2 : 28 <= Kfn 2 6).
      { assert (H2g : forall m, Kfn 2 m = iter (Kfn 1) (2 * m + 2) 0) by reflexivity.
        rewrite H2g. pose proof (HK1 14). replace (2 * 6 + 2) with 14 by lia. lia. }
      assert (HK3 : Kfn 3 0 = Kfn 2 6) by (rewrite HKgen, HK20; reflexivity).
      pose proof (Kfn_step_k 3 0). lia. }
    destruct (rule_2_H_rep (2 * m' + 1) r (Pfn (S r) 0 1) R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    destruct (Ht2 ltac:(lia)) as [Ht2_le Hr2_pos].
    destruct r2 as [| r2']; [lia |].
    exists r2', m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    - unfold H_plus2. replace (2 * S m' - 1) with (2 * m' + 1) by lia.
      eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_H_mono | exact HM17] | exact Hm2].
    - lia.
  Qed.

End Fwp2_HLemmas.
