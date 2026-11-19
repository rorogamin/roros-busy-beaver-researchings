(*
  rocq/Kropitz.v
  Reusable, axiom-free formalization of the 3-state Kropitz f_ω core
  (parameterized by the B2 target state dState).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH.
Import ListNotations.

Definition mkCfgR (st : option nat) (L R : list nat) : Config :=
  match R with
  | [] => mkConfig st L 0 []
  | a :: r' => mkConfig st L a r'
  end.

Definition Reaches (tm : TM) (c1 c2 : Config) (t : nat) : Prop :=
  steps tm t c1 = Some c2.

Lemma reaches_zero : forall tm c, Reaches tm c c 0.
Proof. reflexivity. Qed.

Lemma reaches_trans : forall tm c1 c2 c3 t1 t2,
  Reaches tm c1 c2 t1 -> Reaches tm c2 c3 t2 -> Reaches tm c1 c3 (t1 + t2).
Proof. intros. eapply steps_add; eassumption. Qed.

Lemma step_mkCfgR_R : forall tm q w nx L cur R,
  tm q cur = Some (mkAction (S w) DR nx) ->
  step tm (mkCfgR (Some q) L (cur :: R)) = Some (mkCfgR nx (S w :: L) R).
Proof.
  intros tm q w nx L cur R Ht.
  destruct R; unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_mkCfgR_R_nil : forall tm q w nx L,
  tm q 0 = Some (mkAction (S w) DR nx) ->
  step tm (mkCfgR (Some q) L []) = Some (mkCfgR nx (S w :: L) []).
Proof.
  intros tm q w nx L Ht. unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_mkCfgR_L_cons : forall tm q w a cur nx L R,
  tm q cur = Some (mkAction (S w) DL nx) ->
  step tm (mkCfgR (Some q) (a :: L) (cur :: R)) = Some (mkCfgR nx L (a :: S w :: R)).
Proof.
  intros tm q w a cur nx L R Ht. unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_mkCfgR_L_nil : forall tm q w cur nx R,
  tm q cur = Some (mkAction (S w) DL nx) ->
  step tm (mkCfgR (Some q) [] (cur :: R)) = Some (mkCfgR nx [] (0 :: S w :: R)).
Proof.
  intros tm q w cur nx R Ht. unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_mkCfgR_L_nil_zero : forall tm q cur a nx R,
  tm q cur = Some (mkAction 0 DL nx) ->
  step tm (mkCfgR (Some q) [] (cur :: a :: R)) = Some (mkCfgR nx [] (0 :: 0 :: a :: R)).
Proof.
  intros tm q cur a nx R Ht. unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_mkCfgR_L_cons_zero : forall tm q a cur b nx L R,
  tm q cur = Some (mkAction 0 DL nx) ->
  step tm (mkCfgR (Some q) (a :: L) (cur :: b :: R)) = Some (mkCfgR nx L (a :: 0 :: b :: R)).
Proof.
  intros tm q a cur b nx L R Ht. unfold step, mkCfgR; simpl; rewrite Ht; reflexivity.
Qed.

Lemma rep_snoc_one : forall n s xs, rep n s (s :: xs) = s :: rep n s xs.
Proof.
  intros n. induction n as [| k IH]; intros s xs; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Kropitz Core Specification *)

Record KropitzCore (tm : TM) (dState : nat) : Prop := mkKropitzCore {
  kc_A1 : tm 0 1 = Some (mkAction 3 DL (Some 1));
  kc_A3 : tm 0 3 = Some (mkAction 2 DR (Some 0));
  kc_B1 : tm 1 1 = Some (mkAction 3 DR (Some 1));
  kc_B2 : tm 1 2 = Some (mkAction 1 DL (Some dState));
  kc_B3 : tm 1 3 = Some (mkAction 2 DR (Some 0));
  kc_C0 : tm 2 0 = Some (mkAction 3 DR (Some 1));
  kc_C1 : tm 2 1 = Some (mkAction 1 DL (Some 1));
  kc_C2 : tm 2 2 = Some (mkAction 3 DL (Some 2));
  kc_C3 : tm 2 3 = Some (mkAction 2 DR (Some 2));
  kc_D0 : tm dState 0 = Some (mkAction 3 DR (Some 1));
  kc_D2 : tm dState 2 = Some (mkAction 3 DL (Some 2));
  kc_D3 : tm dState 3 = Some (mkAction 2 DR (Some 2))
}.

Definition Bcfg (k m : nat) (R : list nat) : Config :=
  mkCfgR (Some 0) (rep (S k) 2 (rep (2 * m + 1) 3 [])) R.

Fixpoint Kfn (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => S m
  | S j => fun m => iter (Kfn j) (2 * m + 2) 0
  end.

Lemma Kfn_ge_succ : forall k m, S m <= Kfn k m.
Proof.
  induction k as [| j IH]; intro m.
  - simpl; lia.
  - change (S m <= iter (Kfn j) (2 * m + 2) 0).
    replace (2 * m + 2) with ((2 * m + 1) + 1) by lia.
    rewrite iter_add.
    change (iter (Kfn j) 1 0) with (Kfn j 0).
    pose proof (IH 0) as H0.
    pose proof (iter_ge_add_pos (Kfn j) (fun x _ => IH x) (2 * m + 1) (Kfn j 0) ltac:(lia)).
    lia.
Qed.

Lemma Kfn_mono : forall k x y, x <= y -> Kfn k x <= Kfn k y.
Proof.
  induction k as [| j IH]; intros x y Hxy; simpl.
  - lia.
  - apply iter_mono_steps.
    + intro z. pose proof (Kfn_ge_succ j z). lia.
    + lia.
Qed.

Lemma Kfn_ge_fFin : forall k m, fFin k m <= Kfn k m.
Proof.
  induction k as [| j IH]; intro m.
  - unfold fFin, fPlus, fZero; simpl; lia.
  - change (iter (fFin j) m m <= iter (Kfn j) (2 * m + 2) 0).
    replace (2 * m + 2) with (m + (m + 2)) by lia.
    rewrite iter_add.
    assert (Hbase : m <= iter (Kfn j) (m + 2) 0).
    { assert (Hg : forall n, n <= iter (Kfn j) n 0).
      { intro n. induction n as [| p IHp]; simpl; [lia |].
        pose proof (Kfn_ge_succ j (iter (Kfn j) p 0)). lia. }
      pose proof (Hg (m + 2)). lia. }
    assert (Hfn : forall n x, iter (fFin j) n x <= iter (Kfn j) n x).
    { intro n. induction n as [| p IHp]; intro x; simpl; [lia |].
      eapply Nat.le_trans; [apply (fgh_mono _ (fFin_props j)); apply IHp | apply IH]. }
    eapply Nat.le_trans; [apply Hfn |].
    apply iter_mono_arg; [apply Kfn_mono | exact Hbase].
Qed.

Lemma Kfn_zero_ge : forall k, S k <= Kfn k 0.
Proof.
  induction k as [| j IH]; simpl; [lia |].
  pose proof (Kfn_ge_succ j (Kfn j 0)). lia.
Qed.

Lemma Kfn_step_k : forall k m, Kfn k m <= Kfn (S k) m.
Proof.
  intros k m. change (Kfn k m <= iter (Kfn k) (2 * m + 2) 0).
  replace (2 * m + 2) with (1 + (2 * m + 1)) by lia.
  rewrite iter_add.
  change (iter (Kfn k) 1 (iter (Kfn k) (2 * m + 1) 0)) with (Kfn k (iter (Kfn k) (2 * m + 1) 0)).
  apply Kfn_mono.
  assert (Hg : forall n, n <= iter (Kfn k) n 0).
  { intro n. induction n as [| p IHp]; simpl; [lia |].
    pose proof (Kfn_ge_succ k (iter (Kfn k) p 0)). lia. }
  pose proof (Hg (2 * m + 1)). lia.
Qed.

Lemma Kfn_mono_k : forall k1 k2 m, k1 <= k2 -> Kfn k1 m <= Kfn k2 m.
Proof.
  intros k1 k2 m Hk. induction Hk as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply Kfn_step_k].
Qed.

Section CoreLemmas.
  Variable tm : TM.
  Variable dState : nat.
  Hypothesis hc : KropitzCore tm dState.

  Lemma loop_B1 : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 1 R)) (mkCfgR (Some 1) (rep n 3 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ.
      + apply (step_mkCfgR_R tm 1 2 (Some 1) L 1 (rep k 1 R) (kc_B1 _ _ hc)).
      + specialize (IH (3 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_A3 : forall n L R,
    Reaches tm (mkCfgR (Some 0) L (rep n 3 R)) (mkCfgR (Some 0) (rep n 2 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ.
      + apply (step_mkCfgR_R tm 0 1 (Some 0) L 3 (rep k 3 R) (kc_A3 _ _ hc)).
      + specialize (IH (2 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_C3 : forall n L R,
    Reaches tm (mkCfgR (Some 2) L (rep n 3 R)) (mkCfgR (Some 2) (rep n 2 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ.
      + apply (step_mkCfgR_R tm 2 1 (Some 2) L 3 (rep k 3 R) (kc_C3 _ _ hc)).
      + specialize (IH (2 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma loop_C2 : forall n L R,
    Reaches tm (mkCfgR (Some 2) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 2) L (2 :: rep n 3 R)) n.
  Proof.
    induction n as [| k IH]; intros L R.
    - apply reaches_zero.
    - eapply steps_succ.
      + apply (step_mkCfgR_L_cons tm 2 2 2 2 (Some 2) (rep k 2 L) R (kc_C2 _ _ hc)).
      + specialize (IH L (3 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma step_B2_3 : forall L R,
    Reaches tm (mkCfgR (Some 1) (3 :: L) (2 :: R)) (mkCfgR (Some 1) L (2 :: 1 :: R)) 3.
  Proof.
    intros L R.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 3 2 _ L R (kc_B2 _ _ hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ dState 1 _ L 3 (1 :: R) (kc_D3 _ _ hc)) |].
    apply steps_one. apply (step_mkCfgR_L_cons _ 2 0 2 1 _ L R (kc_C1 _ _ hc)).
  Qed.

  Lemma loop_B2_3 : forall j L R,
    Reaches tm (mkCfgR (Some 1) (rep j 3 L) (2 :: R))
               (mkCfgR (Some 1) L (2 :: rep j 1 R)) (3 * j).
  Proof.
    induction j as [| k IH]; intros L R.
    - apply reaches_zero.
    - replace (3 * S k) with (3 + 3 * k) by lia.
      eapply reaches_trans; [apply step_B2_3 |].
      specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma step_B2_2k : forall k L R,
    Reaches tm (mkCfgR (Some 1) (rep (S k) 2 (3 :: L)) (2 :: R))
               (mkCfgR (Some 1) (rep (S k) 2 L) (2 :: 1 :: R)) (2 * k + 5).
  Proof.
    intros k L R. destruct k as [| k'].
    - simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ (3 :: L) R (kc_B2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ dState 2 3 2 _ L (1 :: R) (kc_D2 _ _ hc)) |].
      change 3 with (2 + 1).
      eapply reaches_trans; [apply (loop_C3 2 L (1 :: R)) |].
      apply steps_one. apply (step_mkCfgR_L_cons _ 2 0 2 1 _ (2 :: L) R (kc_C1 _ _ hc)).
    - replace (2 * S k' + 5) with (S (S (k' + S ((k' + 3) + 1)))) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ (rep (S k') 2 (3 :: L)) R (kc_B2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ dState 2 2 2 _ (rep k' 2 (3 :: L)) (1 :: R) (kc_D2 _ _ hc)) |].
      eapply reaches_trans; [apply (loop_C2 k' (3 :: L) (3 :: 1 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 2 3 2 _ L (rep k' 3 (3 :: 1 :: R)) (kc_C2 _ _ hc)) |].
      assert (Hrep : 3 :: 3 :: rep k' 3 (3 :: 1 :: R) = rep (k' + 3) 3 (1 :: R)).
      { rewrite rep_snoc_one. replace (k' + 3) with (S (S (S k'))) by lia. reflexivity. }
      rewrite Hrep.
      eapply reaches_trans; [apply (loop_C3 (k' + 3) L (1 :: R)) |].
      replace (k' + 3) with (S (S (S k'))) by lia. simpl.
      apply steps_one. apply (step_mkCfgR_L_cons _ 2 0 2 1 _ _ R (kc_C1 _ _ hc)).
  Qed.

  Lemma loop_B2_2k : forall k j L R,
    Reaches tm (mkCfgR (Some 1) (rep (S k) 2 (rep j 3 L)) (2 :: R))
               (mkCfgR (Some 1) (rep (S k) 2 L) (2 :: rep j 1 R)) ((2 * k + 5) * j).
  Proof.
    intros k j. induction j as [| m IH]; intros L R.
    - replace ((2 * k + 5) * 0) with 0 by lia. apply reaches_zero.
    - replace ((2 * k + 5) * S m) with ((2 * k + 5) + (2 * k + 5) * m) by lia.
      eapply reaches_trans; [apply step_B2_2k |].
      specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Lemma bounce_B_nil : forall n R,
    Reaches tm (mkCfgR (Some 1) [] (2 :: rep n 1 R))
               (mkCfgR (Some 1) (rep (n + 2) 3 []) R) (n + 3).
  Proof.
    intros n R.
    replace (n + 3) with (S (S (S n))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 1 0 2 _ (rep n 1 R) (kc_B2 _ _ hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ dState 2 _ [] 0 (1 :: rep n 1 R) (kc_D0 _ _ hc)) |].
    pose proof (loop_B1 (S n) [3] R) as H.
    rewrite rep_snoc_one in H.
    replace (n + 2) with (S (S n)) by lia. exact H.
  Qed.

  Lemma bounce_B_2k_nil : forall k R,
    Reaches tm (mkCfgR (Some 1) (rep (S k) 2 []) (2 :: R))
               (mkCfgR (Some 0) (rep (S k) 2 [3]) (1 :: R)) (2 * k + 4).
  Proof.
    intros k R. destruct k as [| k'].
    - simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ [] R (kc_B2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ dState 2 2 _ (1 :: R) (kc_D2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [] 0 (3 :: 1 :: R) (kc_C0 _ _ hc)) |].
      apply steps_one. apply (step_mkCfgR_R _ 1 1 _ [3] 3 (1 :: R) (kc_B3 _ _ hc)).
    - replace (2 * S k' + 4) with (S (S (k' + S (S (S (S k')))))) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ (rep (S k') 2 []) R (kc_B2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ dState 2 2 2 _ (rep k' 2 []) (1 :: R) (kc_D2 _ _ hc)) |].
      eapply reaches_trans; [apply (loop_C2 k' [] (3 :: 1 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 2 2 2 _ (rep k' 3 (3 :: 1 :: R)) (kc_C2 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [] 0 (3 :: rep k' 3 (3 :: 1 :: R)) (kc_C0 _ _ hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 _ [3] 3 (rep k' 3 (3 :: 1 :: R)) (kc_B3 _ _ hc)) |].
      rewrite rep_snoc_one.
      pose proof (loop_A3 (S k') [2; 3] (1 :: R)) as H.
      rewrite rep_snoc_one in H. exact H.
  Qed.

  Lemma kropitz_level0_from_B : forall m R,
    Reaches tm (mkCfgR (Some 1) (rep (2 * m + 1) 3 []) (2 :: R))
               (mkCfgR (Some 1) (rep (2 * m + 3) 3 []) R) (8 * m + 7).
  Proof.
    intros m R.
    replace (8 * m + 7) with (3 * (2 * m + 1) + ((2 * m + 1) + 3)) by lia.
    eapply reaches_trans; [apply loop_B2_3 |].
    replace (2 * m + 3) with ((2 * m + 1) + 2) by lia.
    apply bounce_B_nil.
  Qed.

  Lemma kropitz_levelS_from_B : forall k m R,
    Reaches tm (mkCfgR (Some 1) (rep (S k) 2 (rep (2 * m + 1) 3 [])) (2 :: R))
               (Bcfg k 0 (rep (2 * m + 2) 1 R)) ((2 * k + 5) * (2 * m + 1) + (2 * k + 4)).
  Proof.
    intros k m R.
    eapply reaches_trans; [apply loop_B2_2k |].
    replace (rep (2 * m + 2) 1 R) with (1 :: rep (2 * m + 1) 1 R).
    - unfold Bcfg. simpl. apply bounce_B_2k_nil.
    - replace (2 * m + 2) with (S (2 * m + 1)) by lia. reflexivity.
  Qed.

  Lemma kropitz_K1 : forall m R,
    Reaches tm (Bcfg 0 m (1 :: R)) (Bcfg 0 (S m) R) (8 * m + 9).
  Proof.
    intros m R. unfold Bcfg.
    replace (8 * m + 9) with (S ((8 * m + 7) + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ (rep (2 * m + 1) 3 []) R (kc_A1 _ _ hc)) |].
    eapply reaches_trans; [apply kropitz_level0_from_B |].
    replace (2 * S m + 1) with (2 * m + 3) by lia.
    apply steps_one. apply (step_mkCfgR_R _ 1 1 _ (rep (2 * m + 3) 3 []) 3 R (kc_B3 _ _ hc)).
  Qed.

  Lemma kropitz_K2 : forall k m R,
    Reaches tm (Bcfg (S k) m (1 :: R))
               (Bcfg k 0 (rep (2 * m + 2) 1 (3 :: R)))
               (S ((2 * k + 5) * (2 * m + 1) + (2 * k + 4))).
  Proof.
    intros k m R. unfold Bcfg.
    eapply steps_succ.
    - apply (step_mkCfgR_L_cons _ 0 2 2 1 _ (rep (S k) 2 (rep (2 * m + 1) 3 [])) R (kc_A1 _ _ hc)).
    - apply kropitz_levelS_from_B.
  Qed.

  Lemma kropitz_step : forall k m R,
    exists t, Reaches tm (Bcfg k m (1 :: R)) (Bcfg k (Kfn k m) R) t /\ 1 <= t.
  Proof.
    induction k as [| j IH].
    - intros m R. exists (8 * m + 9). split; [apply kropitz_K1 | lia].
    - assert (Hiter : forall n m R,
        exists t, Reaches tm (Bcfg j m (rep n 1 R)) (Bcfg j (iter (Kfn j) n m) R) t).
      { intro n. induction n as [| p IHp]; intros m R.
        - exists 0. apply reaches_zero.
        - destruct (IH m (rep p 1 R)) as [t1 [H1 _]].
          destruct (IHp (Kfn j m) R) as [t2 H2].
          exists (t1 + t2).
          replace (iter (Kfn j) (S p) m) with (iter (Kfn j) p (Kfn j m)).
          + eapply reaches_trans; [exact H1 | exact H2].
          + replace (S p) with (p + 1) by lia. rewrite iter_add. reflexivity. }
      intros m R.
      pose proof (kropitz_K2 j m R) as H1.
      destruct (Hiter (2 * m + 2) 0 (3 :: R)) as [t2 H2].
      assert (H3 : step tm (Bcfg j (Kfn (S j) m) (3 :: R)) = Some (Bcfg (S j) (Kfn (S j) m) R)).
      { unfold Bcfg. apply (step_mkCfgR_R _ 0 1 _ _ 3 R (kc_A3 _ _ hc)). }
      exists ((S ((2 * j + 5) * (2 * m + 1) + (2 * j + 4)) + t2) + 1).
      split; [| lia].
      eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | apply steps_one; exact H3].
  Qed.

  Lemma kropitz_rep : forall k n m R,
    exists t, Reaches tm (Bcfg k m (rep n 1 R)) (Bcfg k (iter (Kfn k) n m) R) t.
  Proof.
    intros k n. induction n as [| p IH]; intros m R.
    - exists 0. apply reaches_zero.
    - destruct (kropitz_step k m (rep p 1 R)) as [t1 [H1 _]].
      destruct (IH (Kfn k m) R) as [t2 H2].
      exists (t1 + t2).
      replace (iter (Kfn k) (S p) m) with (iter (Kfn k) p (Kfn k m)).
      + eapply reaches_trans; [exact H1 | exact H2].
      + replace (S p) with (p + 1) by lia. rewrite iter_add. reflexivity.
  Qed.

End CoreLemmas.
