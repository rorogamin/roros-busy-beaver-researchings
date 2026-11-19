(*
  rocq/Fwm2.v
  Reusable, axiom-free formalization of the 6-state Fwm2 (f_{ω×2}) core
  built directly on top of KropitzCore tm 3.
  Powers BB(6, 7), BB(6, 8), and BB(6, 9).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Record Fwm2Core (tm : TM) : Prop := mkFwm2Core {
  fw_kc : KropitzCore tm 3;
  fw_A4 : tm 0 4 = Some (mkAction 4 DL (Some 1));
  fw_B4 : tm 1 4 = Some (mkAction 3 DL (Some 5));
  fw_C4 : tm 2 4 = Some (mkAction 4 DL (Some 2));
  fw_C5 : tm 2 5 = Some (mkAction 0 DL (Some 4));
  fw_D5 : tm 3 5 = Some (mkAction 3 DR (Some 4));
  fw_E0 : tm 4 0 = Some (mkAction 5 DR (Some 2));
  fw_E1 : tm 4 1 = Some (mkAction 3 DR (Some 4));
  fw_E3 : tm 4 3 = Some (mkAction 4 DL (Some 2));
  fw_F0 : tm 5 0 = Some (mkAction 5 DR (Some 1));
  fw_F3 : tm 5 3 = Some (mkAction 1 DL (Some 5))
}.

Definition B5cfg (k m : nat) (R : list nat) : Config :=
  mkCfgR (Some 0) (rep (S k) 2 (rep (2 * m + 1) 3 [5])) R.

Fixpoint Wexit (k : nat) : nat -> nat :=
  match k with
  | 0 => fun M => S M
  | S j => fun M => Wexit j (Kfn (S j) M)
  end.

Fixpoint Wfn (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => Wexit (2 * m + 2) 0
  | S j => fun m => iter (Wfn j) (2 * m + 2) 0
  end.

(* Mathematical Growth Properties of Wexit and Wfn *)

Lemma Wexit_ge : forall k M, S M <= Wexit k M.
Proof.
  induction k as [| j IH]; intro M.
  - simpl; lia.
  - change (S M <= Wexit j (Kfn (S j) M)).
    pose proof (IH (Kfn (S j) M)).
    pose proof (Kfn_ge_succ (S j) M). lia.
Qed.

Lemma Wexit_mono_M : forall k x y, x <= y -> Wexit k x <= Wexit k y.
Proof.
  induction k as [| j IH]; intros x y Hxy.
  - simpl; lia.
  - change (Wexit j (Kfn (S j) x) <= Wexit j (Kfn (S j) y)).
    apply IH. apply Kfn_mono. exact Hxy.
Qed.

Lemma Wexit_step_k : forall k M, Wexit k M <= Wexit (S k) M.
Proof.
  intros k M. change (Wexit k M <= Wexit k (Kfn (S k) M)).
  apply Wexit_mono_M. pose proof (Kfn_ge_succ (S k) M). lia.
Qed.

Lemma Wexit_mono_k : forall k1 k2 M, k1 <= k2 -> Wexit k1 M <= Wexit k2 M.
Proof.
  intros k1 k2 M Hk. induction Hk as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply Wexit_step_k].
Qed.

Lemma Wfn_zero_0 : Wfn 0 0 = 15.
Proof. reflexivity. Qed.

Lemma Wfn_zero_gt_f_omega : forall m, f_omega m < Wfn 0 m.
Proof.
  intro m.
  assert (H1 : S (Kfn (2 * m + 2) 0) <= Wexit (2 * m + 2) 0).
  { replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    change (S (Kfn (S (2 * m + 1)) 0) <= Wexit (2 * m + 1) (Kfn (S (2 * m + 1)) 0)).
    apply Wexit_ge. }
  assert (H2 : Kfn (2 * m + 2) 0 = Kfn (2 * m + 1) (Kfn (2 * m + 1) 0)).
  { replace (2 * m + 2) with (S (2 * m + 1)) by lia. reflexivity. }
  assert (H3 : m <= Kfn (2 * m + 1) 0).
  { pose proof (Kfn_zero_ge (2 * m + 1)). lia. }
  assert (H4 : Kfn (2 * m + 1) m <= Kfn (2 * m + 2) 0).
  { rewrite H2. apply Kfn_mono. exact H3. }
  assert (H5 : fFin m m <= Kfn (2 * m + 1) m).
  { eapply Nat.le_trans; [apply Kfn_ge_fFin | apply Kfn_mono_k; lia]. }
  change (fFin m m < Wexit (2 * m + 2) 0). lia.
Qed.

Lemma Wfn_ge_succ : forall k m, S m <= Wfn k m.
Proof.
  induction k as [| j IH]; intro m.
  - pose proof (Wfn_zero_gt_f_omega m).
    pose proof (fgh_ge_self _ (fOmegaMul_props 1 0) m).
    change (f_omega m) with (fOmegaMul 1 0 m) in *. lia.
  - change (S m <= iter (Wfn j) (2 * m + 2) 0).
    replace (2 * m + 2) with ((2 * m + 1) + 1) by lia.
    rewrite iter_add.
    change (iter (Wfn j) 1 0) with (Wfn j 0).
    pose proof (IH 0) as H0.
    pose proof (iter_ge_add_pos (Wfn j) (fun x _ => IH x) (2 * m + 1) (Wfn j 0) ltac:(lia)).
    lia.
Qed.

Lemma Wfn_mono : forall k x y, x <= y -> Wfn k x <= Wfn k y.
Proof.
  induction k as [| j _]; intros x y Hxy.
  - change (Wexit (2 * x + 2) 0 <= Wexit (2 * y + 2) 0).
    apply Wexit_mono_k; lia.
  - change (iter (Wfn j) (2 * x + 2) 0 <= iter (Wfn j) (2 * y + 2) 0).
    apply iter_mono_steps; [intro z; pose proof (Wfn_ge_succ j z); lia | lia].
Qed.

Lemma Wfn_zero_ge : forall k, k + 15 <= Wfn k 0.
Proof.
  induction k as [| j IH].
  - rewrite Wfn_zero_0; lia.
  - change (S j + 15 <= Wfn j (Wfn j 0)).
    pose proof (Wfn_ge_succ j (Wfn j 0)). lia.
Qed.

Lemma Wfn_step_k : forall k m, Wfn k m <= Wfn (S k) m.
Proof.
  intros k m. change (Wfn k m <= iter (Wfn k) (2 * m + 2) 0).
  replace (2 * m + 2) with (1 + (2 * m + 1)) by lia.
  rewrite iter_add.
  change (iter (Wfn k) 1 (iter (Wfn k) (2 * m + 1) 0)) with (Wfn k (iter (Wfn k) (2 * m + 1) 0)).
  apply Wfn_mono.
  assert (Hg : forall n, n <= iter (Wfn k) n 0).
  { intro n. induction n as [| p IHp]; simpl; [lia |].
    pose proof (Wfn_ge_succ k (iter (Wfn k) p 0)). lia. }
  pose proof (Hg (2 * m + 1)). lia.
Qed.

Lemma Wfn_mono_k : forall k1 k2 m, k1 <= k2 -> Wfn k1 m <= Wfn k2 m.
Proof.
  intros k1 k2 m Hk. induction Hk as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply Wfn_step_k].
Qed.

Lemma Wfn_gt_f_omega_plus : forall k m, f_omega_plus k m < Wfn k m.
Proof.
  induction k as [| j IH]; intro m.
  - apply Wfn_zero_gt_f_omega.
  - destruct m as [| m'].
    + change (0 < Wfn (S j) 0). pose proof (Wfn_ge_succ (S j) 0). lia.
    + change (iter (f_omega_plus j) (S m') (S m') < iter (Wfn j) (2 * S m' + 2) 0).
      replace (2 * S m' + 2) with (S m' + (m' + 3)) by lia.
      rewrite iter_add.
      assert (Hbase : S m' <= iter (Wfn j) (m' + 3) 0).
      { assert (Hg : forall n, n <= iter (Wfn j) n 0).
        { intro n. induction n as [| p IHp]; simpl; [lia |].
          pose proof (Wfn_ge_succ j (iter (Wfn j) p 0)). lia. }
        pose proof (Hg (m' + 3)). lia. }
      pose proof (iter_strict_dom (Wfn j) (f_omega_plus j) 0 (fun z _ => IH z)
        (fOmegaMul_props 1 j) (S m') (S m') ltac:(lia) ltac:(lia)) as Hlt.
      pose proof (iter_mono_arg (Wfn j) (fun x y h => Wfn_mono j x y h) (S m') (S m') _ Hbase) as Harg.
      lia.
Qed.

Lemma Wfn_succ_zero_gt_f_omega_mul2 : forall n, f_omega_mul2 n < Wfn (S n) 0.
Proof.
  intro n.
  change (f_omega_plus n n < Wfn n (Wfn n 0)).
  pose proof (Wfn_gt_f_omega_plus n n) as H1.
  assert (H2 : n <= Wfn n 0) by (pose proof (Wfn_zero_ge n); lia).
  pose proof (Wfn_mono n n (Wfn n 0) H2) as H3.
  lia.
Qed.

(* Operational Engine Lemmas *)

Section Fwm2Lemmas.
  Variable tm : TM.
  Hypothesis hf : Fwm2Core tm.

  Local Lemma loop_E1 : forall n L R,
    Reaches tm (mkCfgR (Some 4) L (rep n 1 R)) (mkCfgR (Some 4) (rep n 3 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ L 1 _ (fw_E1 _ hf)) |].
      specialize (IH (3 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_F3 : forall n L R,
    Reaches tm (mkCfgR (Some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R (fw_F3 _ hf)) |].
      specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_C_4 : forall n j L R,
    exists t, Reaches tm (mkCfgR (Some 2) (rep n 3 L) (2 :: rep j 3 (4 :: R)))
                         (mkCfgR (Some 2) L (2 :: rep (j + n) 3 (4 :: R))) t.
  Proof.
    induction n as [| k IH]; intros j L R.
    - exists 0. replace (j + 0) with j by lia. apply reaches_zero.
    - destruct (IH (S j) L R) as [t2 Hrest].
      replace (S j + k) with (j + S k) in Hrest by lia.
      eexists. eapply reaches_trans; [| exact Hrest].
      eapply reaches_trans.
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 2 3 2 _ _ _ (kc_C2 _ _ (fw_kc _ hf))) |].
        change (3 :: 3 :: rep j 3 (4 :: R)) with (rep (S (S j)) 3 (4 :: R)).
        apply (loop_C3 tm 3 (fw_kc _ hf) (S (S j)) (rep k 3 L) (4 :: R)).
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 3 2 4 _ _ R (fw_C4 _ hf)) |].
        apply (loop_C2 tm 3 (fw_kc _ hf) (S j) (rep k 3 L) (4 :: R)).
  Qed.

  Local Lemma fwm2_level0_entry : forall m R,
    exists t, Reaches tm (B5cfg 0 m (1 :: R)) (Bcfg (2 * m + 2) 0 (4 :: R)) t.
  Proof.
    intros m R.
    destruct (loop_C_4 (2 * m + 2) 0 [] R) as [tC HC]. simpl in HC.
    eexists. eapply reaches_trans.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ (rep (2 * m + 1) 3 [5]) R (kc_A1 _ _ (fw_kc _ hf))) |].
      eapply reaches_trans; [apply (loop_B2_3 tm 3 (fw_kc _ hf) (2 * m + 1) [5] (3 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 5 2 _ [] _ (kc_B2 _ _ (fw_kc _ hf))) |].
      replace (1 :: rep (2 * m + 1) 1 (3 :: R)) with (rep (2 * m + 2) 1 (3 :: R))
        by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ [] 5 _ (fw_D5 _ hf)) |].
      pose proof (loop_E1 (2 * m + 2) [3] (3 :: R)) as HE.
      rewrite rep_snoc_one in HE. exact HE.
    - replace (rep (2 * m + 3) 3 []) with (3 :: rep (2 * m + 2) 3 [])
        by (replace (2 * m + 3) with (S (2 * m + 2)) by lia; reflexivity).
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 3 3 3 _ (rep (2 * m + 2) 3 []) R (fw_E3 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 1 _ _ 3 (4 :: R) (kc_C3 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 3 2 4 _ _ R (fw_C4 _ hf)) |].
      eapply reaches_trans; [exact HC |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 2 2 2 _ _ (kc_C2 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [] 0 _ (kc_C0 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 _ [3] 3 _ (kc_B3 _ _ (fw_kc _ hf))) |].
      pose proof (loop_A3 tm 3 (fw_kc _ hf) (2 * m + 2) [2; 3] (4 :: R)) as HA.
      rewrite rep_snoc_one in HA. exact HA.
  Qed.

  Local Lemma fwm2_exit : forall k M R,
    exists t, Reaches tm (Bcfg k M (4 :: R)) (B5cfg 0 (Wexit k M) R) t /\ Wexit k M <= t.
  Proof.
    induction k as [| j IH]; intros M R.
    - eexists. split.
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 4 _ (rep (2 * M + 1) 3 []) R (fw_A4 _ hf)) |].
        eapply reaches_trans; [apply (kropitz_level0_from_B tm 3 (fw_kc _ hf) M (4 :: R)) |].
        replace (2 * M + 3) with (S (2 * M + 2)) by lia.
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 3 4 _ (rep (2 * M + 2) 3 []) R (fw_B4 _ hf)) |].
        eapply reaches_trans; [apply (loop_F3 (2 * M + 2) [] (3 :: R)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 0 3 _ _ (fw_F3 _ hf)) |].
        change (1 :: rep (2 * M + 2) 1 (3 :: R)) with (rep (S (2 * M + 2)) 1 (3 :: R)).
        eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fw_F0 _ hf)) |].
        eapply reaches_trans; [apply (loop_B1 tm 3 (fw_kc _ hf) (S (2 * M + 2)) [5] (3 :: R)) |].
        apply steps_one.
        unfold B5cfg, Wexit.
        replace (2 * S M + 1) with (S (2 * M + 2)) by lia.
        apply (step_mkCfgR_R _ 1 1 _ _ 3 R (kc_B3 _ _ (fw_kc _ hf))).
      + unfold Wexit. lia.
    - destruct (kropitz_rep tm 3 (fw_kc _ hf) j (2 * M + 2) 0 (4 :: R)) as [t3 H3].
      destruct (IH (Kfn (S j) M) R) as [t4 [H4 Hle4]].
      exists ((S ((2 * j + 5) * (2 * M + 1) + (2 * j + 4)) + t3) + t4).
      split; [| change (Wexit j (Kfn (S j) M) <= (S ((2 * j + 5) * (2 * M + 1) + (2 * j + 4)) + t3) + t4); lia].
      eapply reaches_trans; [eapply reaches_trans; [| exact H3] | exact H4].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 4 _ _ R (fw_A4 _ hf)) |].
      apply (kropitz_levelS_from_B tm 3 (fw_kc _ hf) j M (4 :: R)).
  Qed.

  Local Lemma bounce_B5_2k : forall k R,
    Reaches tm (mkCfgR (Some 1) (rep (S k) 2 [5]) (2 :: R))
               (mkCfgR (Some 0) (rep (S k) 2 [3; 5]) (1 :: R)) (2 * k + 6).
  Proof.
    intros k R. destruct k as [| k'].
    - simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ [5] R (kc_B2 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 2 5 2 _ [] (1 :: R) (kc_D2 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil_zero _ 2 5 3 _ (1 :: R) (fw_C5 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 4 4 _ [] 0 (0 :: 3 :: 1 :: R) (fw_E0 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [5] 0 (3 :: 1 :: R) (kc_C0 _ _ (fw_kc _ hf))) |].
      apply steps_one. apply (step_mkCfgR_R _ 1 1 _ [3; 5] 3 (1 :: R) (kc_B3 _ _ (fw_kc _ hf))).
    - replace (2 * S k' + 6) with (S (S (k' + S (S (S (S (S (S k')))))))) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ (rep (S k') 2 [5]) R (kc_B2 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 2 2 2 _ (rep k' 2 [5]) (1 :: R) (kc_D2 _ _ (fw_kc _ hf))) |].
      eapply reaches_trans; [apply (loop_C2 tm 3 (fw_kc _ hf) k' [5] (3 :: 1 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 2 5 2 _ [] _ (kc_C2 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil_zero _ 2 5 3 _ _ (fw_C5 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 4 4 _ [] 0 _ (fw_E0 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [5] 0 _ (kc_C0 _ _ (fw_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 _ [3; 5] 3 _ (kc_B3 _ _ (fw_kc _ hf))) |].
      rewrite rep_snoc_one.
      pose proof (loop_A3 tm 3 (fw_kc _ hf) (S k') [2; 3; 5] (1 :: R)) as H.
      rewrite rep_snoc_one in H. exact H.
  Qed.

  Theorem fwm2_step : forall k m R,
    exists t, Reaches tm (B5cfg k m (1 :: R)) (B5cfg k (Wfn k m) R) t /\ Wfn k m <= t.
  Proof.
    induction k as [| j IH].
    - intros m R.
      destruct (fwm2_level0_entry m R) as [t1 H1].
      destruct (fwm2_exit (2 * m + 2) 0 R) as [t2 [H2 Hle2]].
      exists (t1 + t2). split; [eapply reaches_trans; eassumption | change (Wexit (2 * m + 2) 0 <= t1 + t2); lia].
    - assert (Hiter : forall n m R,
        exists t, Reaches tm (B5cfg j m (rep n 1 R)) (B5cfg j (iter (Wfn j) n m) R) t /\
                  (1 <= n -> iter (Wfn j) n m <= t)).
      { intro n. induction n as [| p IHp]; intros m R.
        - exists 0. split; [apply reaches_zero | lia].
        - destruct (IH m (rep p 1 R)) as [t1 [H1 Hle1]].
          destruct (IHp (Wfn j m) R) as [t2 [H2 Hle2]].
          exists (t1 + t2).
          replace (iter (Wfn j) (S p) m) with (iter (Wfn j) p (Wfn j m))
            by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
          split; [eapply reaches_trans; eassumption |].
          intros _. destruct p as [| p']; simpl in *; lia. }
      intros m R.
      destruct (Hiter (2 * m + 2) 0 (3 :: R)) as [t4 [H4 Hle4]].
      eexists. split.
      + eapply reaches_trans; [eapply reaches_trans; [| exact H4] |].
        * eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ _ R (kc_A1 _ _ (fw_kc _ hf))) |].
          eapply reaches_trans; [apply (loop_B2_2k tm 3 (fw_kc _ hf) j (2 * m + 1) [5] (3 :: R)) |].
          replace (rep (2 * m + 2) 1 (3 :: R)) with (1 :: rep (2 * m + 1) 1 (3 :: R))
            by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
          apply (bounce_B5_2k j (rep (2 * m + 1) 1 (3 :: R))).
        * apply steps_one. unfold B5cfg.
          apply (step_mkCfgR_R _ 0 1 _ _ 3 R (kc_A3 _ _ (fw_kc _ hf))).
      + pose proof (Hle4 ltac:(lia)) as H4lb.
        change (Wfn (S j) m) with (iter (Wfn j) (2 * m + 2) 0). lia.
  Qed.

End Fwm2Lemmas.
