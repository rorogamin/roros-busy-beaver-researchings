(*
  rocq/Kropitz2.v
  Reusable, axiom-free formalization of our 2-state, 9-symbol exact Kropitz f_ω core
  and generic reload / pass-2 reload / halt combinators for BB(2, m) champions.
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Record Kropitz2Core (tm : TM) : Prop := mkKropitz2Core {
  k2c_A1 : tm 0 1 = Some (mkAction 5 DL (Some 0));
  k2c_A2 : tm 0 2 = Some (mkAction 1 DL (Some 1));
  k2c_A3 : tm 0 3 = Some (mkAction 6 DR (Some 0));
  k2c_A4 : tm 0 4 = Some (mkAction 3 DR (Some 0));
  k2c_A5 : tm 0 5 = Some (mkAction 4 DR (Some 0));
  k2c_A6 : tm 0 6 = Some (mkAction 2 DR (Some 1));
  k2c_A7 : tm 0 7 = Some (mkAction 8 DL (Some 1));
  k2c_A8 : tm 0 8 = Some (mkAction 5 DL (Some 0));
  k2c_B0 : tm 1 0 = Some (mkAction 4 DR (Some 0));
  k2c_B1 : tm 1 1 = Some (mkAction 1 DL (Some 0));
  k2c_B2 : tm 1 2 = Some (mkAction 3 DL (Some 1));
  k2c_B3 : tm 1 3 = Some (mkAction 2 DR (Some 1));
  k2c_B4 : tm 1 4 = Some (mkAction 2 DR (Some 1));
  k2c_B5 : tm 1 5 = Some (mkAction 3 DL (Some 0));
  k2c_B6 : tm 1 6 = Some (mkAction 3 DL (Some 1));
  k2c_B8 : tm 1 8 = Some (mkAction 8 DL (Some 1))
}.

Definition B2cfg (k m : nat) (R : list nat) : Config :=
  mkCfgR (Some 0) (rep (S k) 6 (4 :: rep (2 * m) 3 [])) R.

Lemma Kfn_strict_mono : forall k x y, x < y -> Kfn k x < Kfn k y.
Proof.
  induction k as [| j IH]; intros x y Hxy.
  - simpl. lia.
  - change (iter (Kfn j) (2 * x + 2) 0 < iter (Kfn j) (2 * y + 2) 0). assert (Hsucc : forall z, S z <= Kfn j z) by apply Kfn_ge_succ.
    assert (Hle_fn : forall z, z <= Kfn j z) by (intro z; pose proof (Hsucc z); lia).
    assert (Hle_steps : 2 * x + 2 + 2 <= 2 * y + 2) by lia.
    pose proof (iter_mono_steps (Kfn j) Hle_fn _ _ 0 Hle_steps) as Hmono.
    assert (Hstep1 : iter (Kfn j) (2 * x + 2) 0 < iter (Kfn j) (S (2 * x + 2)) 0).
    { rewrite iter_succ. apply Hsucc. }
    assert (Hstep2 : iter (Kfn j) (S (2 * x + 2)) 0 <= iter (Kfn j) (2 * x + 2 + 2) 0).
    { replace (2 * x + 2 + 2) with (S (S (2 * x + 2))) by lia.
      rewrite iter_succ. pose proof (Hle_fn (iter (Kfn j) (S (2 * x + 2)) 0)). assumption. }
    lia.
Qed.

Lemma iter_Kfn0 : forall n x, iter (Kfn 0) n x = n + x.
Proof.
  induction n as [| k IH]; intro x; simpl; [reflexivity | rewrite IH; change (Kfn 0 (k + x)) with (S (k + x)); lia].
Qed.

Lemma Kfn_1_eq : forall m, Kfn 1 m = 2 * m + 2.
Proof.
  intro m. change (Kfn 1 m) with (iter (Kfn 0) (2 * m + 2) 0).
  rewrite iter_Kfn0. lia.
Qed.

Lemma Kfn_2_step : forall n, iter (Kfn 1) n 0 + 2 = 2 ^ (n + 1).
Proof.
  induction n as [| k IH].
  - simpl. reflexivity.
  - rewrite iter_succ, Kfn_1_eq. replace (S k + 1) with (S (k + 1)) by lia.
    change (2 ^ S (k + 1)) with (2 * 2 ^ (k + 1)). lia.
Qed.

Lemma Kfn_2_0_eq : Kfn 2 0 = 6.
Proof.
  pose proof (Kfn_2_step 2) as H.
  change (iter (Kfn 1) 2 0) with (Kfn 2 0) in H.
  replace (2 ^ (2 + 1)) with 8 in H by reflexivity. lia.
Qed.

Lemma Kfn_3_0_pow : Kfn 3 0 + 2 = 2 ^ 15.
Proof.
  change (Kfn 3 0) with (Kfn 2 (Kfn 2 0)).
  rewrite Kfn_2_0_eq.
  pose proof (Kfn_2_step (2 * 6 + 2)) as H.
  change (iter (Kfn 1) (2 * 6 + 2) 0) with (Kfn 2 6) in H.
  replace (2 * 6 + 2 + 1) with 15 in H by lia.
  exact H.
Qed.

Lemma Kfn_zero_gt_fFin2 : forall k, 3 <= k -> fFin k 2 < Kfn k 0.
Proof.
  induction k as [| j IH]; intro Hk; [lia |].
  assert (Hcase : j = 2 \/ 3 <= j) by lia.
  destruct Hcase as [-> | Hj].
  - change (fFin 3 2) with (fPlus fZero 3 2).
    assert (Hf3 : fPlus fZero 3 2 = 2048).
    { compute. reflexivity. }
    assert (Hpow : 2 ^ 15 = 16 * 2048).
    { replace 15 with (4 + 11) by lia. rewrite Nat.pow_add_r.
      replace (2 ^ 4) with 16 by reflexivity.
      replace (2 ^ 11) with 2048 by (compute; reflexivity). reflexivity. }
    pose proof Kfn_3_0_pow as Hk3. lia.
  - specialize (IH Hj).
    change (fFin (S j) 2) with (fFin j (fFin j 2)).
    pose proof (Kfn_ge_fFin j (fFin j 2)) as H1.
    pose proof (Kfn_strict_mono j _ _ IH) as H2.
    change (Kfn (S j) 0) with (Kfn j (Kfn j 0)).
    lia.
Qed.

Lemma Kfn_zero_gt_fOmega : forall n, f_omega n < Kfn (S n) 0.
Proof.
  intro n. unfold f_omega. rewrite f_omega_eq.
  pose proof (Kfn_ge_fFin n n) as H1.
  pose proof (Kfn_zero_ge n) as Hn.
  pose proof (Kfn_strict_mono n n (Kfn n 0) ltac:(lia)) as H2.
  change (Kfn (S n) 0) with (Kfn n (Kfn n 0)). lia.
Qed.

Section Kropitz2Lemmas.
  Variable tm : TM.
  Hypothesis hc : Kropitz2Core tm.

  Lemma loop_B3_R : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 3 R)) (mkCfgR (Some 1) (rep n 2 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; simpl.
    - apply reaches_zero.
    - eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 (Some 1) L 3 (rep k 3 R) (k2c_B3 _ hc)) |].
      specialize (IH (2 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_A3_R : forall n L R,
    Reaches tm (mkCfgR (Some 0) L (rep n 3 R)) (mkCfgR (Some 0) (rep n 6 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; simpl.
    - apply reaches_zero.
    - eapply steps_succ; [apply (step_mkCfgR_R _ 0 5 (Some 0) L 3 (rep k 3 R) (k2c_A3 _ hc)) |].
      specialize (IH (6 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_B6_L : forall n a L R,
    Reaches tm (mkCfgR (Some 1) (rep n 6 (a :: L)) (6 :: R))
               (mkCfgR (Some 1) L (a :: rep (S n) 3 R)) (S n).
  Proof.
    induction n as [| k IH]; intros a L R; simpl.
    - apply steps_one. apply (step_mkCfgR_L_cons _ 1 2 a 6 (Some 1) L R (k2c_B6 _ hc)).
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 6 6 (Some 1) _ R (k2c_B6 _ hc)) |].
      specialize (IH a L (3 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_B2_L : forall n a L R,
    Reaches tm (mkCfgR (Some 1) (rep n 2 (a :: L)) (2 :: R))
               (mkCfgR (Some 1) L (a :: rep (S n) 3 R)) (S n).
  Proof.
    induction n as [| k IH]; intros a L R; simpl.
    - apply steps_one. apply (step_mkCfgR_L_cons _ 1 2 a 2 (Some 1) L R (k2c_B2 _ hc)).
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 2 2 (Some 1) _ R (k2c_B2 _ hc)) |].
      specialize (IH a L (3 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_B2_L_nil : forall n R,
    Reaches tm (mkCfgR (Some 1) (rep n 2 []) (2 :: R))
               (mkCfgR (Some 1) [] (0 :: rep (S n) 3 R)) (S n).
  Proof.
    induction n as [| k IH]; intros R; simpl.
    - apply steps_one. apply (step_mkCfgR_L_nil _ 1 2 2 (Some 1) R (k2c_B2 _ hc)).
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 2 2 (Some 1) _ R (k2c_B2 _ hc)) |].
      specialize (IH (3 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma step_A2_3 : forall n L R,
    Reaches tm (mkCfgR (Some 0) (rep n 2 (3 :: L)) (2 :: R))
               (mkCfgR (Some 0) (rep n 2 L) (2 :: 1 :: R)) (2 * n + 3).
  Proof.
    intros n L R. destruct n as [| k].
    - simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 0 3 2 (Some 1) L R (k2c_A2 _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 (Some 1) L 3 (1 :: R) (k2c_B3 _ hc)) |].
      apply steps_one. apply (step_mkCfgR_L_cons _ 1 0 2 1 (Some 0) L R (k2c_B1 _ hc)).
    - replace (2 * S k + 3) with (S (S k + (S (S k) + 1))) by lia.
      simpl rep at 1.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 0 2 2 (Some 1) _ R (k2c_A2 _ hc)) |].
      eapply reaches_trans; [apply (loop_B2_L k 3 L (1 :: R)) |].
      change (3 :: rep (S k) 3 (1 :: R)) with (rep (S (S k)) 3 (1 :: R)).
      eapply reaches_trans; [apply (loop_B3_R (S (S k)) L (1 :: R)) |].
      simpl rep at 2.
      apply steps_one. apply (step_mkCfgR_L_cons _ 1 0 2 1 (Some 0) _ R (k2c_B1 _ hc)).
  Qed.

  Lemma loop_A2_3 : forall n j L R,
    Reaches tm (mkCfgR (Some 0) (rep n 2 (rep j 3 L)) (2 :: R))
               (mkCfgR (Some 0) (rep n 2 L) (2 :: rep j 1 R)) ((2 * n + 3) * j).
  Proof.
    intros n j. induction j as [| m IH]; intros L R.
    - replace ((2 * n + 3) * 0) with 0 by lia. apply reaches_zero.
    - replace ((2 * n + 3) * S m) with ((2 * n + 3) + (2 * n + 3) * m) by lia.
      eapply reaches_trans; [apply step_A2_3 |].
      specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma bounce_A2_nil : forall n R,
    Reaches tm (mkCfgR (Some 0) (rep n 2 []) (2 :: R))
               (mkCfgR (Some 0) (rep n 6 [4]) (1 :: R)) (2 * n + 2).
  Proof.
    intros n R. destruct n as [| k].
    - simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 0 0 2 (Some 1) R (k2c_A2 _ hc)) |].
      apply steps_one. apply (step_mkCfgR_R _ 1 3 (Some 0) [] 0 (1 :: R) (k2c_B0 _ hc)).
    - replace (2 * S k + 2) with (S (S k + S (S k))) by lia.
      simpl rep at 1.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 0 2 2 (Some 1) _ R (k2c_A2 _ hc)) |].
      eapply reaches_trans; [apply (loop_B2_L_nil k (1 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 3 (Some 0) [] 0 _ (k2c_B0 _ hc)) |].
      apply (loop_A3_R (S k) [4] (1 :: R)).
  Qed.

  Lemma loop_A1_4 : forall n L R,
    Reaches tm (mkCfgR (Some 0) (4 :: L) (rep n 1 R))
               (mkCfgR (Some 0) (4 :: rep n 3 L) R) (3 * n).
  Proof.
    induction n as [| k IH]; intros L R.
    - replace (3 * 0) with 0 by lia. apply reaches_zero.
    - replace (3 * S k) with (S (S (S (3 * k)))) by lia.
      simpl rep at 1.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 4 4 1 (Some 0) L (rep k 1 R) (k2c_A1 _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 2 (Some 0) L 4 (5 :: rep k 1 R) (k2c_A4 _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 0 3 (Some 0) (3 :: L) 5 (rep k 1 R) (k2c_A5 _ hc)) |].
      specialize (IH (3 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma kropitz2_entry : forall s, (s = 1 \/ s = 8) -> forall k m R,
    Reaches tm (B2cfg k m (s :: R))
               (mkCfgR (Some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (2 :: 3 :: R)) 3.
  Proof.
    intros s Hs k m R.
    assert (HAs : tm 0 s = Some (mkAction 5 DL (Some 0))).
    { destruct Hs as [-> | ->]; [apply (k2c_A1 _ hc) | apply (k2c_A8 _ hc)]. }
    unfold B2cfg. simpl rep at 1.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 4 6 s (Some 0) _ R HAs) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 (Some 1) _ 6 (5 :: R) (k2c_A6 _ hc)) |].
    apply steps_one. apply (step_mkCfgR_L_cons _ 1 2 2 5 (Some 0) _ R (k2c_B5 _ hc)).
  Qed.

  Lemma kropitz2_K1 : forall s, (s = 1 \/ s = 8) -> forall m R,
    Reaches tm (B2cfg 0 m (s :: R)) (B2cfg 0 (S m) R) (12 * m + 15).
  Proof.
    intros s Hs m R.
    replace (12 * m + 15) with (3 + (3 + ((2 * 0 + 3) * (2 * m) + (2 * 0 + 2 + (3 * (2 * m + 2) + 1))))) by lia.
    eapply reaches_trans; [apply (kropitz2_entry s Hs 0 m R) |].
    simpl rep at 1.
    eapply reaches_trans.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 0 4 2 (Some 1) (rep (2 * m) 3 []) (3 :: R) (k2c_A2 _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 (Some 1) (rep (2 * m) 3 []) 4 (1 :: 3 :: R) (k2c_B4 _ hc)) |].
      apply steps_one. apply (step_mkCfgR_L_cons _ 1 0 2 1 (Some 0) (rep (2 * m) 3 []) (3 :: R) (k2c_B1 _ hc)).
    - eapply reaches_trans; [apply (loop_A2_3 0 (2 * m) [] (1 :: 3 :: R)) |].
      eapply reaches_trans; [apply (bounce_A2_nil 0 (rep (2 * m) 1 (1 :: 3 :: R))) |].
      replace (1 :: rep (2 * m) 1 (1 :: 3 :: R)) with (rep (2 * m + 2) 1 (3 :: R))
        by (rewrite rep_snoc_one; replace (2 * m + 2) with (S (S (2 * m))) by lia; reflexivity).
      eapply reaches_trans; [apply (loop_A1_4 (2 * m + 2) [] (3 :: R)) |].
      apply steps_one. unfold B2cfg.
      replace (2 * S m) with (2 * m + 2) by lia.
      apply (step_mkCfgR_R _ 0 5 (Some 0) (4 :: rep (2 * m + 2) 3 []) 3 R (k2c_A3 _ hc)).
  Qed.

  Lemma kropitz2_K2 : forall s, (s = 1 \/ s = 8) -> forall j m R,
    Reaches tm (B2cfg (S j) m (s :: R))
               (B2cfg j 0 (rep (2 * m + 2) 1 (3 :: R)))
               ((2 * j + 5) * (2 * m) + 4 * j + 12).
  Proof.
    intros s Hs j m R.
    replace ((2 * j + 5) * (2 * m) + 4 * j + 12) with
      (3 + S (S j + S (S j + S ((2 * S j + 3) * (2 * m) + (2 * S j + 2)))))
      by (replace (2 * S j + 3) with (2 * j + 5) by lia; lia).
    eapply reaches_trans; [apply (kropitz2_entry s Hs (S j) m R) |].
    simpl rep at 1.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 0 6 2 (Some 1) _ (3 :: R) (k2c_A2 _ hc)) |].
    eapply reaches_trans; [apply (loop_B6_L j 4 (rep (2 * m) 3 []) (1 :: 3 :: R)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 (Some 1) (rep (2 * m) 3 []) 4 (rep (S j) 3 (1 :: 3 :: R)) (k2c_B4 _ hc)) |].
    eapply reaches_trans; [apply (loop_B3_R (S j) (2 :: rep (2 * m) 3 []) (1 :: 3 :: R)) |].
    replace (rep (S j) 2 (2 :: rep (2 * m) 3 [])) with (rep (S (S j)) 2 (rep (2 * m) 3 []))
      by (rewrite rep_snoc_one; reflexivity).
    simpl rep at 1.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 1 (Some 0) _ (3 :: R) (k2c_B1 _ hc)) |].
    eapply reaches_trans; [apply (loop_A2_3 (S j) (2 * m) [] (1 :: 3 :: R)) |].
    pose proof (bounce_A2_nil (S j) (rep (2 * m) 1 (1 :: 3 :: R))) as Hb.
    replace (1 :: rep (2 * m) 1 (1 :: 3 :: R)) with (rep (2 * m + 2) 1 (3 :: R)) in Hb
      by (rewrite rep_snoc_one; replace (2 * m + 2) with (S (S (2 * m))) by lia; reflexivity).
    exact Hb.
  Qed.

  Lemma kropitz2_step : forall k m R,
    exists t, Reaches tm (B2cfg k m (1 :: R)) (B2cfg k (Kfn k m) R) t /\ Kfn k m <= t.
  Proof.
    induction k as [| j IH].
    - intros m R. exists (12 * m + 15). split; [apply (kropitz2_K1 1 (or_introl eq_refl)) | unfold Kfn; lia].
    - assert (Hiter : forall n m R,
        exists t, Reaches tm (B2cfg j m (rep n 1 R)) (B2cfg j (iter (Kfn j) n m) R) t /\
                  (1 <= n -> iter (Kfn j) n m <= t)).
      { intro n. induction n as [| p IHp]; intros m R.
        - exists 0. split; [apply reaches_zero | lia].
        - destruct (IH m (rep p 1 R)) as [t1 [H1 Hk1]].
          destruct (IHp (Kfn j m) R) as [t2 [H2 Hle2]].
          exists (t1 + t2).
          assert (Hcomm : iter (Kfn j) p (Kfn j m) = iter (Kfn j) (S p) m).
          { replace (S p) with (p + 1) by lia. rewrite iter_add. reflexivity. }
          rewrite Hcomm in H2. split.
          + eapply reaches_trans; [exact H1 | exact H2].
          + intros _. destruct p as [| p'].
            * rewrite <- Hcomm. simpl iter. lia.
            * rewrite Hcomm in Hle2. pose proof (Hle2 ltac:(lia)). lia. }
      intros m R.
      pose proof (kropitz2_K2 1 (or_introl eq_refl) j m R) as H1.
      destruct (Hiter (2 * m + 2) 0 (3 :: R)) as [t2 [H2 Hle2]].
      assert (H3 : step tm (B2cfg j (Kfn (S j) m) (3 :: R)) = Some (B2cfg (S j) (Kfn (S j) m) R)).
      { unfold B2cfg. apply (step_mkCfgR_R _ 0 5 (Some 0) _ 3 R (k2c_A3 _ hc)). }
      exists (((2 * j + 5) * (2 * m) + 4 * j + 12 + t2) + 1).
      split.
      + eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | apply steps_one; exact H3].
      + pose proof (Hle2 ltac:(lia)) as H2le.
        change (Kfn (S j) m) with (iter (Kfn j) (2 * m + 2) 0). lia.
  Qed.

  Lemma kropitz2_step_8 : forall k m R,
    exists t, Reaches tm (B2cfg k m (8 :: R)) (B2cfg k (Kfn k m) R) t /\ Kfn k m <= t.
  Proof.
    intros k m R. destruct k as [| j].
    - exists (12 * m + 15). split; [apply (kropitz2_K1 8 (or_intror eq_refl)) | unfold Kfn; lia].
    - assert (Hiter : forall n m' R',
        exists t, Reaches tm (B2cfg j m' (rep n 1 R')) (B2cfg j (iter (Kfn j) n m') R') t /\
                  (1 <= n -> iter (Kfn j) n m' <= t)).
      { intro n. induction n as [| p IHp]; intros m' R'.
        - exists 0. split; [apply reaches_zero | lia].
        - destruct (kropitz2_step j m' (rep p 1 R')) as [t1 [H1 Hk1]].
          destruct (IHp (Kfn j m') R') as [t2 [H2 Hle2]].
          exists (t1 + t2).
          assert (Hcomm : iter (Kfn j) p (Kfn j m') = iter (Kfn j) (S p) m').
          { replace (S p) with (p + 1) by lia. rewrite iter_add. reflexivity. }
          rewrite Hcomm in H2. split.
          + eapply reaches_trans; [exact H1 | exact H2].
          + intros _. destruct p as [| p'].
            * rewrite <- Hcomm. simpl iter. lia.
            * rewrite Hcomm in Hle2. pose proof (Hle2 ltac:(lia)). lia. }
      pose proof (kropitz2_K2 8 (or_intror eq_refl) j m R) as H1.
      destruct (Hiter (2 * m + 2) 0 (3 :: R)) as [t2 [H2 Hle2]].
      assert (H3 : step tm (B2cfg j (Kfn (S j) m) (3 :: R)) = Some (B2cfg (S j) (Kfn (S j) m) R)).
      { unfold B2cfg. apply (step_mkCfgR_R _ 0 5 (Some 0) _ 3 R (k2c_A3 _ hc)). }
      exists (((2 * j + 5) * (2 * m) + 4 * j + 12 + t2) + 1).
      split.
      + eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | apply steps_one; exact H3].
      + pose proof (Hle2 ltac:(lia)) as H2le.
        change (Kfn (S j) m) with (iter (Kfn j) (2 * m + 2) 0). lia.
  Qed.

  (* Reload / Pass-2 / Halt Combinators *)

  Lemma reload_bounce_loop : forall w' (htBw : tm 1 (S w') = Some (mkAction (S w') DL (Some 1))) j m2 R,
    exists t, Reaches tm (mkCfgR (Some 1) (rep (S m2) 2 (rep j 3 [])) (S w' :: R))
                         (mkCfgR (Some 1) (rep (m2 + j + 1) 2 []) (S w' :: R)) t.
  Proof.
    intros w' htBw. induction j as [| j' IH]; intros m2 R.
    - replace (m2 + 0 + 1) with (S m2) by lia. exists 0. apply reaches_zero.
    - simpl rep at 1.
      eassert (H1 : step tm (mkCfgR (Some 1) (2 :: rep m2 2 (3 :: rep j' 3 [])) (S w' :: R)) =
                    Some (mkCfgR (Some 1) (rep m2 2 (3 :: rep j' 3 [])) (2 :: S w' :: R))).
      { apply (step_mkCfgR_L_cons _ 1 w' 2 (S w') (Some 1) _ R htBw). }
      pose proof (loop_B2_L m2 3 (rep j' 3 []) (S w' :: R)) as H2.
      pose proof (loop_B3_R (S (S m2)) (rep j' 3 []) (S w' :: R)) as H3.
      change (3 :: rep (S m2) 3 (S w' :: R)) with (rep (S (S m2)) 3 (S w' :: R)) in H2.
      destruct (IH (S m2) R) as [t2 Hrec].
      replace (S m2 + j' + 1) with (m2 + S j' + 1) in Hrec by lia.
      eexists. eapply reaches_trans.
      + eapply steps_succ; [exact H1 | eapply reaches_trans; [exact H2 | exact H3]].
      + exact Hrec.
  Qed.

  Lemma reload_from_4 : forall w' (htBw : tm 1 (S w') = Some (mkAction (S w') DL (Some 1))) k m R,
    exists t, Reaches tm (mkCfgR (Some 1) (rep (2 * m) 3 []) (4 :: rep (S k) 3 (S w' :: R)))
                         (B2cfg (2 * m + k + 1) 0 (S w' :: R)) t /\ 1 <= t.
  Proof.
    intros w' htBw k m R.
    assert (H1 : step tm (mkCfgR (Some 1) (rep (2 * m) 3 []) (4 :: rep (S k) 3 (S w' :: R))) =
                 Some (mkCfgR (Some 1) (2 :: rep (2 * m) 3 []) (rep (S k) 3 (S w' :: R)))).
    { apply (step_mkCfgR_R _ 1 1 (Some 1) _ 4 _ (k2c_B4 _ hc)). }
    pose proof (loop_B3_R (S k) (2 :: rep (2 * m) 3 []) (S w' :: R)) as H2.
    replace (rep (S k) 2 (2 :: rep (2 * m) 3 [])) with (rep (S (S k)) 2 (rep (2 * m) 3 [])) in H2
      by (rewrite rep_snoc_one; reflexivity).
    destruct (reload_bounce_loop w' htBw (2 * m) (S k) R) as [t3 H3].
    replace (S k + 2 * m + 1) with (S (2 * m + k + 1)) in H3 by lia.
    assert (H4 : step tm (mkCfgR (Some 1) (2 :: rep (2 * m + k + 1) 2 []) (S w' :: R)) =
                 Some (mkCfgR (Some 1) (rep (2 * m + k + 1) 2 []) (2 :: S w' :: R))).
    { apply (step_mkCfgR_L_cons _ 1 w' 2 (S w') (Some 1) _ R htBw). }
    pose proof (loop_B2_L_nil (2 * m + k + 1) (S w' :: R)) as H5.
    assert (H6 : step tm (mkCfgR (Some 1) [] (0 :: rep (S (2 * m + k + 1)) 3 (S w' :: R))) =
                 Some (mkCfgR (Some 0) [4] (rep (S (2 * m + k + 1)) 3 (S w' :: R)))).
    { apply (step_mkCfgR_R _ 1 3 (Some 0) [] 0 _ (k2c_B0 _ hc)). }
    pose proof (loop_A3_R (S (2 * m + k + 1)) [4] (S w' :: R)) as H7.
    change (mkCfgR (Some 0) (rep (S (2 * m + k + 1)) 6 [4]) (S w' :: R))
      with (B2cfg (2 * m + k + 1) 0 (S w' :: R)) in H7.
    eexists. split.
    - eapply reaches_trans.
      + eapply steps_succ; [exact H1 | eapply reaches_trans; [exact H2 | exact H3]].
      + eapply steps_succ; [exact H4 | eapply reaches_trans; [exact H5 | eapply steps_succ; [exact H6 | exact H7]]].
    - lia.
  Qed.

  Lemma kropitz2_reload_gen : forall s w',
    tm 0 s = Some (mkAction (S w') DL (Some 1)) ->
    tm 1 (S w') = Some (mkAction (S w') DL (Some 1)) ->
    forall k m R,
      exists t, Reaches tm (B2cfg k m (s :: R)) (B2cfg (2 * m + k + 1) 0 (S w' :: R)) t /\ 1 <= t.
  Proof.
    intros s w' HtAs HtBw k m R. unfold B2cfg. simpl rep at 1.
    assert (H1 : step tm (mkCfgR (Some 0) (6 :: rep k 6 (4 :: rep (2 * m) 3 [])) (s :: R)) =
                 Some (mkCfgR (Some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: S w' :: R))).
    { apply (step_mkCfgR_L_cons _ 0 w' 6 s (Some 1) _ R HtAs). }
    pose proof (loop_B6_L k 4 (rep (2 * m) 3 []) (S w' :: R)) as H2.
    destruct (reload_from_4 w' HtBw k m R) as [t3 [H3 _]].
    eexists. split.
    - eapply steps_succ; [exact H1 | eapply reaches_trans; [exact H2 | exact H3]].
    - lia.
  Qed.

  Lemma kropitz2_pass2_reload : forall w',
    tm 0 9 = Some (mkAction 10 DL (Some 0)) ->
    tm 1 10 = Some (mkAction (S w') DL (Some 1)) ->
    tm 1 (S w') = Some (mkAction (S w') DL (Some 1)) ->
    forall k m,
      exists t, Reaches tm (B2cfg k m [9]) (B2cfg (2 * m + k + 1) 0 [S w']) t /\ 1 <= t.
  Proof.
    intros w' HtA9 HtB10 HtBw k m. unfold B2cfg. simpl rep at 1.
    assert (H1 : step tm (mkCfgR (Some 0) (6 :: rep k 6 (4 :: rep (2 * m) 3 [])) [9]) =
                 Some (mkCfgR (Some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) [6; 10])).
    { apply (step_mkCfgR_L_cons _ 0 9 6 9 (Some 0) _ [] HtA9). }
    assert (H2 : step tm (mkCfgR (Some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) [6; 10]) =
                 Some (mkCfgR (Some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) [10])).
    { apply (step_mkCfgR_R _ 0 1 (Some 1) _ 6 [10] (k2c_A6 _ hc)). }
    assert (H3 : step tm (mkCfgR (Some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) [10]) =
                 Some (mkCfgR (Some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) [2; S w'])).
    { apply (step_mkCfgR_L_cons _ 1 w' 2 10 (Some 1) _ [] HtB10). }
    assert (H4 : exists t4, Reaches tm (mkCfgR (Some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) [2; S w'])
                                       (mkCfgR (Some 1) (rep (2 * m) 3 []) (4 :: rep (S k) 3 [S w'])) t4).
    { destruct k as [| k'].
      - exists 1. apply steps_one. apply (step_mkCfgR_L_cons _ 1 2 4 2 (Some 1) (rep (2 * m) 3 []) [S w'] (k2c_B2 _ hc)).
      - simpl rep at 1.
        pose proof (loop_B6_L k' 4 (rep (2 * m) 3 []) [3; S w']) as Hs2.
        rewrite rep_snoc_one in Hs2.
        eexists. eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 6 2 (Some 1) _ [S w'] (k2c_B2 _ hc)) | exact Hs2]. }
    destruct H4 as [t4 H4].
    destruct (reload_from_4 w' HtBw k m []) as [t5 [H5 _]].
    eexists. split.
    - eapply steps_succ; [exact H1 | eapply steps_succ; [exact H2 | eapply steps_succ; [exact H3 | eapply reaches_trans; [exact H4 | exact H5]]]].
    - lia.
  Qed.

  Lemma kropitz2_halt :
    tm 0 0 = Some (mkAction 9 DL (Some 1)) ->
    tm 1 9 = Some (mkAction 1 DR None) ->
    forall k m, HaltsIn tm (B2cfg k m []) (2 * k + 5).
  Proof.
    intros HtA0 HtB9 k m.
    replace (2 * k + 5) with (S ((S k) + S ((S k) + 1))) by lia.
    assert (H1 : step tm (B2cfg k m []) =
                 Some (mkCfgR (Some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) [6; 9])).
    { unfold B2cfg, mkCfgR, step. simpl. rewrite HtA0. reflexivity. }
    pose proof (loop_B6_L k 4 (rep (2 * m) 3 []) [9]) as H2.
    assert (H3 : step tm (mkCfgR (Some 1) (rep (2 * m) 3 []) (4 :: rep (S k) 3 [9])) =
                 Some (mkCfgR (Some 1) (2 :: rep (2 * m) 3 []) (rep (S k) 3 [9]))).
    { apply (step_mkCfgR_R _ 1 1 (Some 1) _ 4 _ (k2c_B4 _ hc)). }
    pose proof (loop_B3_R (S k) (2 :: rep (2 * m) 3 []) [9]) as H4.
    replace (rep (S k) 2 (2 :: rep (2 * m) 3 [])) with (rep (S (S k)) 2 (rep (2 * m) 3 [])) in H4
      by (rewrite rep_snoc_one; reflexivity).
    assert (H5 : step tm (mkCfgR (Some 1) (rep (S (S k)) 2 (rep (2 * m) 3 [])) [9]) =
                 Some (mkConfig None (1 :: rep (S (S k)) 2 (rep (2 * m) 3 [])) 0 [])).
    { unfold mkCfgR, step. simpl. rewrite HtB9. reflexivity. }
    eexists. split.
    - eapply steps_succ; [exact H1 | eapply reaches_trans; [exact H2 | eapply steps_succ; [exact H3 | eapply reaches_trans; [exact H4 | apply steps_one; exact H5]]]].
    - reflexivity.
  Qed.

End Kropitz2Lemmas.
