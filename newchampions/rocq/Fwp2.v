(*
  rocq/Fwp2.v
  Reusable, axiom-free formalization of the 7-state Fwp2 (f_{ω^2}) core
  (fwp2_6), built directly on top of KropitzCore tm 3.
  Powers ALL BB(7..11, 6..9) champions!
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Record Fwp2Core (tm : TM) : Prop := mkFwp2Core {
  fp_kc : KropitzCore tm 3;
  fp_A4 : tm 0 4 = Some (mkAction 4 DL (Some 1));
  fp_B4 : tm 1 4 = Some (mkAction 3 DL (Some 5));
  fp_B5 : tm 1 5 = Some (mkAction 5 DR (Some 1));
  fp_C4 : tm 2 4 = Some (mkAction 4 DL (Some 2));
  fp_C5 : tm 2 5 = Some (mkAction 1 DL (Some 4));
  fp_D1 : tm 3 1 = Some (mkAction 3 DR (Some 4));
  fp_D5 : tm 3 5 = Some (mkAction 3 DR (Some 3));
  fp_E0 : tm 4 0 = Some (mkAction 5 DR (Some 1));
  fp_E1 : tm 4 1 = Some (mkAction 3 DR (Some 4));
  fp_E3 : tm 4 3 = Some (mkAction 4 DL (Some 2));
  fp_E4 : tm 4 4 = Some (mkAction 3 DL (Some 6));
  fp_E5 : tm 4 5 = Some (mkAction 5 DL (Some 4));
  fp_F0 : tm 5 0 = Some (mkAction 5 DR (Some 1));
  fp_F3 : tm 5 3 = Some (mkAction 1 DL (Some 5));
  fp_G0 : tm 6 0 = Some (mkAction 5 DL (Some 5));
  fp_G3 : tm 6 3 = Some (mkAction 1 DL (Some 6));
  fp_G5 : tm 6 5 = Some (mkAction 5 DL (Some 6))
}.

Definition Scfg (r k m : nat) (R : list nat) : Config :=
  mkCfgR (Some 0) (rep (S k) 2 (rep (2 * m + 1) 3 (rep r 5 []))) R.

Fixpoint PexitOf (step : nat -> nat -> nat) (k : nat) : nat -> nat :=
  match k with
  | 0 => fun M => S M
  | S j => fun M => PexitOf step j (step (S j) M)
  end.

Fixpoint Plevel (prev : nat -> nat -> nat) (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => PexitOf prev (2 * m + 2) 0
  | S j => fun m => iter (Plevel prev j) (2 * m + 2) 0
  end.

Fixpoint Pfn (r : nat) : nat -> nat -> nat :=
  match r with
  | 0 => Kfn
  | S r' => Plevel (Pfn r')
  end.

Definition Pempty (r : nat) : nat := PexitOf (Pfn r) 1 0.

(* Mathematical Growth Properties *)

Record LevelProps (r : nat) (step : nat -> nat -> nat) : Prop := mkLevelProps {
  lp_ge_succ   : forall k m, S m <= step k m;
  lp_mono_m    : forall k x y, x <= y -> step k x <= step k y;
  lp_mono_k    : forall k1 k2 m, k1 <= k2 -> step k1 m <= step k2 m;
  lp_zero_ge   : forall k, S k <= step k 0;
  lp_succ_zero : forall k, step k (step k 0) <= step (S k) 0;
  lp_ge_fgh    : forall k m, fOmegaMul r k m <= step k m
}.

Local Lemma PexitOf_ge : forall step, (forall k m, S m <= step k m) ->
  forall k M, S M <= PexitOf step k M.
Proof.
  intros step Hge k. induction k as [| j IH]; intro M.
  - simpl; lia.
  - change (S M <= PexitOf step j (step (S j) M)).
    pose proof (IH (step (S j) M)). pose proof (Hge (S j) M). lia.
Qed.

Local Lemma PexitOf_mono_M : forall step, (forall k x y, x <= y -> step k x <= step k y) ->
  forall k x y, x <= y -> PexitOf step k x <= PexitOf step k y.
Proof.
  intros step Hmono k. induction k as [| j IH]; intros x y Hxy.
  - simpl; lia.
  - change (PexitOf step j (step (S j) x) <= PexitOf step j (step (S j) y)).
    apply IH, Hmono; exact Hxy.
Qed.

Local Lemma PexitOf_step_k : forall step,
  (forall k m, S m <= step k m) -> (forall k x y, x <= y -> step k x <= step k y) ->
  forall k M, PexitOf step k M <= PexitOf step (S k) M.
Proof.
  intros step Hge Hmono k M.
  change (PexitOf step k M <= PexitOf step k (step (S k) M)).
  apply PexitOf_mono_M; [exact Hmono | pose proof (Hge (S k) M); lia].
Qed.

Local Lemma PexitOf_mono_k : forall step,
  (forall k m, S m <= step k m) -> (forall k x y, x <= y -> step k x <= step k y) ->
  forall k1 k2 M, k1 <= k2 -> PexitOf step k1 M <= PexitOf step k2 M.
Proof.
  intros step Hge Hmono k1 k2 M Hk. induction Hk as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply PexitOf_step_k; assumption].
Qed.

Local Lemma level0_props : LevelProps 0 Kfn.
Proof.
  constructor.
  - apply Kfn_ge_succ.
  - apply Kfn_mono.
  - apply Kfn_mono_k.
  - apply Kfn_zero_ge.
  - intro k. simpl. lia.
  - apply Kfn_ge_fFin.
Qed.

Local Lemma level_step_props : forall r step, LevelProps r step -> LevelProps (S r) (Plevel step).
Proof.
  intros r step [Hge HmonoM HmonoK Hzero HsuccZ Hfgh].
  assert (H0_fgh : forall m, fOmegaMul (S r) 0 m <= Plevel step 0 m).
  { intro m.
    assert (H1 : S (step (2 * m + 2) 0) <= PexitOf step (2 * m + 2) 0).
    { replace (2 * m + 2) with (S (2 * m + 1)) by lia.
      change (S (step (S (2 * m + 1)) 0) <= PexitOf step (2 * m + 1) (step (S (2 * m + 1)) 0)).
      apply PexitOf_ge; exact Hge. }
    assert (H2 : step (2 * m + 1) (step (2 * m + 1) 0) <= step (2 * m + 2) 0).
    { replace (2 * m + 2) with (S (2 * m + 1)) by lia. apply HsuccZ. }
    assert (H3 : m <= step (2 * m + 1) 0) by (pose proof (Hzero (2 * m + 1)); lia).
    assert (H4 : step (2 * m + 1) m <= step (2 * m + 2) 0).
    { eapply Nat.le_trans; [apply HmonoM; exact H3 | exact H2]. }
    assert (H5 : fOmegaMul r m m <= step (2 * m + 1) m).
    { eapply Nat.le_trans; [apply Hfgh | apply HmonoK; lia]. }
    change (fOmegaMul r m m <= PexitOf step (2 * m + 2) 0). lia. }
  assert (HgeS : forall k m, S m <= Plevel step k m).
  { induction k as [| j IH]; intro m.
    - assert (H1 : S (step (2 * m + 2) 0) <= PexitOf step (2 * m + 2) 0).
      { replace (2 * m + 2) with (S (2 * m + 1)) by lia.
        change (S (step (S (2 * m + 1)) 0) <= PexitOf step (2 * m + 1) (step (S (2 * m + 1)) 0)).
        apply PexitOf_ge; exact Hge. }
      pose proof (Hzero (2 * m + 2)). change (S m <= PexitOf step (2 * m + 2) 0). lia.
    - change (S m <= iter (Plevel step j) (2 * m + 2) 0).
      replace (2 * m + 2) with ((2 * m + 1) + 1) by lia.
      rewrite iter_add. change (iter (Plevel step j) 1 0) with (Plevel step j 0).
      pose proof (IH 0) as H0.
      pose proof (iter_ge_add_pos (Plevel step j) (fun x _ => IH x) (2 * m + 1) (Plevel step j 0) ltac:(lia)).
      lia. }
  assert (HmonoMS : forall k x y, x <= y -> Plevel step k x <= Plevel step k y).
  { induction k as [| j _]; intros x y Hxy.
    - change (PexitOf step (2 * x + 2) 0 <= PexitOf step (2 * y + 2) 0).
      apply PexitOf_mono_k; [exact Hge | exact HmonoM | lia].
    - change (iter (Plevel step j) (2 * x + 2) 0 <= iter (Plevel step j) (2 * y + 2) 0).
      apply iter_mono_steps; [intro z; pose proof (HgeS j z); lia | lia]. }
  assert (HstepK : forall k m, Plevel step k m <= Plevel step (S k) m).
  { intros k m. change (Plevel step k m <= iter (Plevel step k) (2 * m + 2) 0).
    replace (2 * m + 2) with (1 + (2 * m + 1)) by lia.
    rewrite iter_add.
    change (iter (Plevel step k) 1 (iter (Plevel step k) (2 * m + 1) 0))
      with (Plevel step k (iter (Plevel step k) (2 * m + 1) 0)).
    apply HmonoMS.
    assert (Hg : forall n, n <= iter (Plevel step k) n 0).
    { intro n. induction n as [| p IHp]; simpl; [lia |].
      pose proof (HgeS k (iter (Plevel step k) p 0)). lia. }
    pose proof (Hg (2 * m + 1)). lia. }
  assert (HmonoKS : forall k1 k2 m, k1 <= k2 -> Plevel step k1 m <= Plevel step k2 m).
  { intros k1 k2 m Hk. induction Hk as [| j Hle IH]; [lia |].
    eapply Nat.le_trans; [exact IH | apply HstepK]. }
  assert (HzeroS : forall k, S k <= Plevel step k 0).
  { induction k as [| j IH]; [apply HgeS |].
    change (S (S j) <= Plevel step j (Plevel step j 0)).
    pose proof (HgeS j (Plevel step j 0)). lia. }
  assert (HfghS : forall k m, fOmegaMul (S r) k m <= Plevel step k m).
  { induction k as [| j IH]; intro m; [apply H0_fgh |].
    change (iter (fOmegaMul (S r) j) m m <= iter (Plevel step j) (2 * m + 2) 0).
    replace (2 * m + 2) with (m + (m + 2)) by lia.
    rewrite (iter_add (Plevel step j)).
    assert (Hbase : m <= iter (Plevel step j) (m + 2) 0).
    { assert (Hg : forall n, n <= iter (Plevel step j) n 0).
      { intro n. induction n as [| p IHp]; simpl; [lia |].
        pose proof (HgeS j (iter (Plevel step j) p 0)). lia. }
      pose proof (Hg (m + 2)). lia. }
    assert (Hfn : forall n x, iter (fOmegaMul (S r) j) n x <= iter (Plevel step j) n x).
    { intro n. induction n as [| p IHp]; intro x; simpl; [lia |].
      eapply Nat.le_trans; [apply (fgh_mono _ (fOmegaMul_props (S r) j)); apply IHp | apply IH]. }
    eapply Nat.le_trans; [apply Hfn | apply iter_mono_arg; [apply HmonoMS | exact Hbase]]. }
  constructor; [exact HgeS | exact HmonoMS | exact HmonoKS | exact HzeroS | intro k; simpl; lia | exact HfghS].
Qed.

Local Lemma Pfn_props : forall r, LevelProps r (Pfn r).
Proof. induction r as [| r' IH]; [apply level0_props | apply level_step_props, IH]. Qed.

Lemma Pfn_ge_succ : forall r k m, S m <= Pfn r k m.
Proof. intro r. apply (lp_ge_succ _ _ (Pfn_props r)). Qed.

Lemma Pfn_mono_m : forall r k x y, x <= y -> Pfn r k x <= Pfn r k y.
Proof. intro r. apply (lp_mono_m _ _ (Pfn_props r)). Qed.

Lemma Pfn_ge_fgh : forall r k m, fOmegaMul r k m <= Pfn r k m.
Proof. intro r. apply (lp_ge_fgh _ _ (Pfn_props r)). Qed.

Lemma Pfn_step_r : forall r k m, Pfn r k m <= Pfn (S r) k m.
Proof.
  intros r k. induction k as [| j IH]; intro m.
  - destruct (Pfn_props r) as [Hge HmonoM HmonoK Hzero HsuccZ _].
    assert (H1 : S (Pfn r (2 * m + 2) 0) <= PexitOf (Pfn r) (2 * m + 2) 0).
    { replace (2 * m + 2) with (S (2 * m + 1)) by lia.
      change (S (Pfn r (S (2 * m + 1)) 0) <= PexitOf (Pfn r) (2 * m + 1) (Pfn r (S (2 * m + 1)) 0)).
      apply PexitOf_ge; exact Hge. }
    assert (H2 : Pfn r (2 * m + 1) (Pfn r (2 * m + 1) 0) <= Pfn r (2 * m + 2) 0).
    { replace (2 * m + 2) with (S (2 * m + 1)) by lia. apply HsuccZ. }
    assert (H3 : m <= Pfn r (2 * m + 1) 0) by (pose proof (Hzero (2 * m + 1)); lia).
    assert (H4 : Pfn r 0 m <= Pfn r (2 * m + 1) m) by (apply HmonoK; lia).
    assert (H5 : Pfn r (2 * m + 1) m <= Pfn r (2 * m + 1) (Pfn r (2 * m + 1) 0)) by (apply HmonoM; exact H3).
    change (Pfn r 0 m <= PexitOf (Pfn r) (2 * m + 2) 0). lia.
  - assert (HP : Pfn r (S j) m = iter (Pfn r j) (2 * m + 2) 0) by (destruct r; reflexivity).
    rewrite HP.
    change (iter (Pfn r j) (2 * m + 2) 0 <= iter (Pfn (S r) j) (2 * m + 2) 0).
    assert (Hfn : forall n x, iter (Pfn r j) n x <= iter (Pfn (S r) j) n x).
    { intro n. induction n as [| p IHp]; intro x; simpl; [lia |].
      eapply Nat.le_trans; [apply Pfn_mono_m; apply IHp | apply IH]. }
    apply Hfn.
Qed.

Lemma Pfn_mono_r : forall r1 r2 k m, r1 <= r2 -> Pfn r1 k m <= Pfn r2 k m.
Proof.
  intros r1 r2 k m Hr. induction Hr as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply Pfn_step_r].
Qed.

Lemma Pfn_r_zero_ge : forall r, S r <= Pfn r 0 0.
Proof.
  induction r as [| r' IH]; [simpl; lia |].
  destruct (Pfn_props r') as [Hge _ HmonoK _ _ _].
  assert (H1 : S (Pfn r' 2 0) <= Pfn (S r') 0 0).
  { change (S (Pfn r' 2 0) <= PexitOf (Pfn r') 1 (Pfn r' 2 0)).
    apply PexitOf_ge; exact Hge. }
  assert (H2 : Pfn r' 0 0 <= Pfn r' 2 0) by (apply HmonoK; lia).
  lia.
Qed.

Lemma Pempty_mono : forall r1 r2, r1 <= r2 -> Pempty r1 <= Pempty r2.
Proof.
  intros r1 r2 Hr. change (S (Pfn r1 1 0) <= S (Pfn r2 1 0)).
  pose proof (Pfn_mono_r r1 r2 1 0 Hr). lia.
Qed.

Lemma Pempty_ge : forall r, r + 2 <= Pempty r.
Proof.
  intro r. change (r + 2 <= S (Pfn r 1 0)).
  pose proof (Pfn_r_zero_ge r).
  pose proof (lp_mono_k _ _ (Pfn_props r) 0 1 0 ltac:(lia)). lia.
Qed.

Theorem Pempty_gt_f_omega2 : forall r, f_omega2 r < Pempty r.
Proof.
  intro r. change (fOmegaMul r 0 r < S (Pfn r 1 0)).
  pose proof (Pfn_ge_fgh r 0 r) as H1.
  assert (H2 : r <= Pfn r 0 0) by (pose proof (Pfn_r_zero_ge r); lia).
  pose proof (Pfn_mono_m r 0 r (Pfn r 0 0) H2) as H3.
  pose proof (lp_succ_zero _ _ (Pfn_props r) 0) as H4. lia.
Qed.

(* Operational Engine Lemmas *)

Section Fwp2Lemmas.
  Variable tm : TM.
  Hypothesis hf : Fwp2Core tm.

  Local Lemma loop_B5 : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 5 R)) (mkCfgR (Some 1) (rep n 5 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 4 _ L 5 _ (fp_B5 _ hf)) |].
    specialize (IH (5 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_E1 : forall n L R,
    Reaches tm (mkCfgR (Some 4) L (rep n 1 R)) (mkCfgR (Some 4) (rep n 3 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ L 1 _ (fp_E1 _ hf)) |].
    specialize (IH (3 :: L) R). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_E5 : forall n L R,
    Reaches tm (mkCfgR (Some 4) (rep n 5 L) (5 :: R)) (mkCfgR (Some 4) L (5 :: rep n 5 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 4 5 5 _ _ R (fp_E5 _ hf)) |].
    specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_F3 : forall n L R,
    Reaches tm (mkCfgR (Some 5) (rep n 3 L) (3 :: R)) (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R (fp_F3 _ hf)) |].
    specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_G3 : forall n L R,
    Reaches tm (mkCfgR (Some 6) (rep n 3 L) (3 :: R)) (mkCfgR (Some 6) L (3 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 3 3 _ _ R (fp_G3 _ hf)) |].
    specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
  Qed.

  Local Lemma loop_G5 : forall n L R,
    Reaches tm (mkCfgR (Some 6) (rep n 5 L) (5 :: R)) (mkCfgR (Some 6) L (5 :: rep n 5 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 4 5 5 _ _ R (fp_G5 _ hf)) |].
    specialize (IH L (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
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
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 2 3 2 _ _ _ (kc_C2 _ _ (fp_kc _ hf))) |].
        change (3 :: 3 :: rep j 3 (4 :: R)) with (rep (S (S j)) 3 (4 :: R)).
        apply (loop_C3 tm 3 (fp_kc _ hf) (S (S j)) (rep k 3 L) (4 :: R)).
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 3 2 4 _ _ R (fp_C4 _ hf)) |].
        apply (loop_C2 tm 3 (fp_kc _ hf) (S j) (rep k 3 L) (4 :: R)).
  Qed.

  Local Lemma bounce_C5_E_B : forall r' R,
    exists t, Reaches tm (mkCfgR (Some 2) (rep r' 5 []) (5 :: R))
                         (mkCfgR (Some 1) (rep (S r') 5 []) (1 :: R)) t.
  Proof.
    intros r' R. destruct r' as [| r''].
    - eexists.
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 2 0 5 _ R (fp_C5 _ hf)) |].
      apply steps_one. apply (step_mkCfgR_R _ 4 4 _ [] 0 (1 :: R) (fp_E0 _ hf)).
    - eexists.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 0 5 5 _ (rep r'' 5 []) R (fp_C5 _ hf)) |].
      eapply reaches_trans; [apply (loop_E5 r'' [] (1 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 4 4 5 _ _ (fp_E5 _ hf)) |].
      change (5 :: rep r'' 5 (1 :: R)) with (rep (S r'') 5 (1 :: R)).
      eapply steps_succ; [apply (step_mkCfgR_R _ 4 4 _ [] 0 _ (fp_E0 _ hf)) |].
      pose proof (loop_B5 (S r'') [5] (1 :: R)) as HB.
      rewrite rep_snoc_one in HB. exact HB.
  Qed.

  Local Lemma bounce_C2_5r : forall r q R,
    exists t, Reaches tm (mkCfgR (Some 2) (rep r 5 []) (2 :: rep q 3 R))
                         (mkCfgR (Some 0) (rep (S q) 2 (3 :: rep r 5 [])) R) t.
  Proof.
    intros r q R. destruct r as [| r'].
    - eexists.
      eapply steps_succ; [apply (step_mkCfgR_L_nil _ 2 2 2 _ _ (kc_C2 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [] 0 _ (kc_C0 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 _ [3] 3 _ (kc_B3 _ _ (fp_kc _ hf))) |].
      pose proof (loop_A3 tm 3 (fp_kc _ hf) q [2; 3] R) as HA.
      rewrite rep_snoc_one in HA. exact HA.
    - destruct (bounce_C5_E_B r' (3 :: rep q 3 R)) as [tm1 Hm1].
      eexists.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 2 5 2 _ _ _ (kc_C2 _ _ (fp_kc _ hf))) |].
      eapply reaches_trans; [exact Hm1 |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 1 1 _ _ 3 _ (kc_B3 _ _ (fp_kc _ hf))) |].
      pose proof (loop_A3 tm 3 (fp_kc _ hf) q (2 :: 3 :: rep (S r') 5 []) R) as HA.
      rewrite rep_snoc_one in HA. exact HA.
  Qed.

  Local Lemma fwp2_level0_entry : forall r m R,
    exists t, Reaches tm (Scfg (S r) 0 m (1 :: R)) (Scfg r (2 * m + 2) 0 (4 :: R)) t.
  Proof.
    intros r m R.
    destruct (loop_C_4 (2 * m + 2) 0 (rep r 5 []) R) as [tC HC].
    rewrite Nat.add_0_l in HC.
    destruct (bounce_C2_5r r (2 * m + 2) (4 :: R)) as [tB HB].
    eexists. eapply reaches_trans.
    - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ _ R (kc_A1 _ _ (fp_kc _ hf))) |].
      eapply reaches_trans; [apply (loop_B2_3 tm 3 (fp_kc _ hf) (2 * m + 1) (rep (S r) 5 []) (3 :: R)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 5 2 _ _ _ (kc_B2 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ (fp_D5 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 1 _ (fp_D1 _ hf)) |].
      pose proof (loop_E1 (2 * m + 1) (3 :: 3 :: rep r 5 []) (3 :: R)) as HE.
      rewrite rep_snoc_one, rep_snoc_one in HE. exact HE.
    - replace (S (S (2 * m + 1))) with (S (2 * m + 2)) by lia.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 3 3 3 _ _ R (fp_E3 _ hf)) |].
      eapply steps_succ; [apply (step_mkCfgR_R _ 2 1 _ _ 3 (4 :: R) (kc_C3 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 3 2 4 _ _ R (fp_C4 _ hf)) |].
      replace (3 :: rep (2 * m + 1) 3 (rep r 5 [])) with (rep (2 * m + 2) 3 (rep r 5 []))
        by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
      eapply reaches_trans; [exact HC | exact HB].
  Qed.

  Local Lemma fwp2_empty3_entry : forall r R,
    exists t, Reaches tm (mkCfgR (Some 0) (2 :: rep (S r) 5 []) (1 :: R))
                         (Scfg r 1 0 (4 :: R)) t.
  Proof.
    intros r R.
    destruct (loop_C_4 1 0 (rep r 5 []) R) as [tC HC].
    rewrite Nat.add_0_l in HC.
    destruct (bounce_C2_5r r 1 (4 :: R)) as [tB HB].
    eexists.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ _ R (kc_A1 _ _ (fp_kc _ hf))) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 5 2 _ _ _ (kc_B2 _ _ (fp_kc _ hf))) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ (fp_D5 _ hf)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 1 _ (fp_D1 _ hf)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 3 3 3 _ _ R (fp_E3 _ hf)) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 2 1 _ _ 3 (4 :: R) (kc_C3 _ _ (fp_kc _ hf))) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 2 3 2 4 _ _ R (fp_C4 _ hf)) |].
    eapply reaches_trans; [exact HC | exact HB].
  Qed.

  Local Lemma bounce_S_2k : forall r k R,
    exists t, Reaches tm (mkCfgR (Some 1) (rep (S k) 2 (rep r 5 [])) (2 :: R))
                         (mkCfgR (Some 0) (rep (S k) 2 (3 :: rep r 5 [])) (1 :: R)) t.
  Proof.
    intros r k R. destruct k as [| k'].
    - destruct r as [| r'].
      + exists 4.
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ [] R (kc_B2 _ _ (fp_kc _ hf))) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil _ 3 2 2 _ (1 :: R) (kc_D2 _ _ (fp_kc _ hf))) |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ [] 0 (3 :: 1 :: R) (kc_C0 _ _ (fp_kc _ hf))) |].
        apply steps_one. apply (step_mkCfgR_R _ 1 1 _ [3] 3 (1 :: R) (kc_B3 _ _ (fp_kc _ hf))).
      + destruct (bounce_C5_E_B r' (3 :: 1 :: R)) as [tm1 Hm1].
        eexists.
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ _ R (kc_B2 _ _ (fp_kc _ hf))) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 2 5 2 _ _ (1 :: R) (kc_D2 _ _ (fp_kc _ hf))) |].
        eapply reaches_trans; [exact Hm1 |].
        eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ _ 1 _ (kc_B1 _ _ (fp_kc _ hf))) |].
        apply steps_one. apply (step_mkCfgR_R _ 1 1 _ _ 3 (1 :: R) (kc_B3 _ _ (fp_kc _ hf))).
    - destruct (bounce_C2_5r r (S k') (1 :: R)) as [tB HB].
      eexists.
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 2 2 _ _ R (kc_B2 _ _ (fp_kc _ hf))) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 2 2 2 _ _ (1 :: R) (kc_D2 _ _ (fp_kc _ hf))) |].
      eapply reaches_trans; [apply (loop_C2 tm 3 (fp_kc _ hf) k' (rep r 5 []) (3 :: 1 :: R)) |].
      rewrite rep_snoc_one. exact HB.
  Qed.

  Local Lemma fwp2_exit_zero : forall r M R,
    exists t, Reaches tm (Scfg r 0 M (4 :: R)) (Scfg (S r) 0 (S M) R) t /\ S M <= t.
  Proof.
    intros r M R. destruct r as [| r'].
    - eexists. split.
      + eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 4 _ _ R (fp_A4 _ hf)) |].
        eapply reaches_trans; [apply (kropitz_level0_from_B tm 3 (fp_kc _ hf) M (4 :: R)) |].
        replace (2 * M + 3) with (S (2 * M + 2)) by lia.
        eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 3 4 _ _ R (fp_B4 _ hf)) |].
        eapply reaches_trans; [apply (loop_F3 (2 * M + 2) [] (3 :: R)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 0 3 _ _ (fp_F3 _ hf)) |].
        change (1 :: rep (2 * M + 2) 1 (3 :: R)) with (rep (S (2 * M + 2)) 1 (3 :: R)).
        eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ hf)) |].
        eapply reaches_trans; [apply (loop_B1 tm 3 (fp_kc _ hf) (S (2 * M + 2)) [5] (3 :: R)) |].
        apply steps_one. unfold Scfg.
        replace (2 * S M + 1) with (S (2 * M + 2)) by lia.
        apply (step_mkCfgR_R _ 1 1 _ _ 3 R (kc_B3 _ _ (fp_kc _ hf))).
      + lia.
    - assert (Hback : exists tb, Reaches tm
        (mkCfgR (Some 6) (rep r' 5 []) (3 :: rep (2 * M + 2) 1 (3 :: R)))
        (mkCfgR (Some 1) (rep (S (S r')) 5 []) (rep (S (2 * M + 2)) 1 (3 :: R))) tb).
      { destruct r' as [| r''].
        - exists 4.
          eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 0 3 _ _ (fp_G3 _ hf)) |].
          change (1 :: rep (2 * M + 2) 1 (3 :: R)) with (rep (S (2 * M + 2)) 1 (3 :: R)).
          eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 0 _ _ (fp_G0 _ hf)) |].
          eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ hf)) |].
          apply steps_one. apply (step_mkCfgR_R _ 1 4 _ [5] 5 _ (fp_B5 _ hf)).
        - eexists.
          eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 5 3 _ _ _ (fp_G3 _ hf)) |].
          change (1 :: rep (2 * M + 2) 1 (3 :: R)) with (rep (S (2 * M + 2)) 1 (3 :: R)).
          eapply reaches_trans; [apply (loop_G5 r'' [] (rep (S (2 * M + 2)) 1 (3 :: R))) |].
          eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 5 _ _ (fp_G5 _ hf)) |].
          change (5 :: rep r'' 5 (rep (S (2 * M + 2)) 1 (3 :: R))) with (rep (S r'') 5 (rep (S (2 * M + 2)) 1 (3 :: R))).
          eapply steps_succ; [apply (step_mkCfgR_L_nil _ 6 4 0 _ _ (fp_G0 _ hf)) |].
          change (5 :: rep (S r'') 5 (rep (S (2 * M + 2)) 1 (3 :: R))) with (rep (S (S r'')) 5 (rep (S (2 * M + 2)) 1 (3 :: R))).
          eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ (fp_F0 _ hf)) |].
          pose proof (loop_B5 (S (S r'')) [5] (rep (S (2 * M + 2)) 1 (3 :: R))) as HB.
          rewrite rep_snoc_one in HB. exact HB. }
      destruct Hback as [tb Hbackp].
      eexists. split.
      + eapply reaches_trans.
        * eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 4 _ _ R (fp_A4 _ hf)) |].
          eapply reaches_trans; [apply (loop_B2_3 tm 3 (fp_kc _ hf) (2 * M + 1) (rep (S r') 5 []) (4 :: R)) |].
          eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 0 5 2 _ _ _ (kc_B2 _ _ (fp_kc _ hf))) |].
          eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 5 _ (fp_D5 _ hf)) |].
          eapply steps_succ; [apply (step_mkCfgR_R _ 3 2 _ _ 1 _ (fp_D1 _ hf)) |].
          pose proof (loop_E1 (2 * M + 1) (3 :: 3 :: rep r' 5 []) (4 :: R)) as HE.
          rewrite rep_snoc_one, rep_snoc_one in HE. exact HE.
        * replace (S (S (2 * M + 1))) with (S (2 * M + 2)) by lia.
          eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 2 3 4 _ _ R (fp_E4 _ hf)) |].
          replace (3 :: rep (2 * M + 1) 3 (rep r' 5 [])) with (rep (2 * M + 2) 3 (rep r' 5 []))
            by (replace (2 * M + 2) with (S (2 * M + 1)) by lia; reflexivity).
          eapply reaches_trans; [apply (loop_G3 (2 * M + 2) (rep r' 5 []) (3 :: R)) |].
          eapply reaches_trans; [exact Hbackp |].
          eapply reaches_trans; [apply (loop_B1 tm 3 (fp_kc _ hf) (S (2 * M + 2)) (rep (S (S r')) 5 []) (3 :: R)) |].
          apply steps_one. unfold Scfg.
          replace (2 * S M + 1) with (S (2 * M + 2)) by lia.
          apply (step_mkCfgR_R _ 1 1 _ _ 3 R (kc_B3 _ _ (fp_kc _ hf))).
      + lia.
  Qed.

  Local Lemma fwp2_main : forall r,
    (forall k m R, exists t, Reaches tm (Scfg r k m (1 :: R)) (Scfg r k (Pfn r k m) R) t /\ Pfn r k m <= t) /\
    (forall k M R, exists t, Reaches tm (Scfg r k M (4 :: R)) (Scfg (S r) 0 (PexitOf (Pfn r) k M) R) t /\
                             PexitOf (Pfn r) k M <= t).
  Proof.
    assert (Hrep : forall r0 k,
      (forall m R, exists t, Reaches tm (Scfg r0 k m (1 :: R)) (Scfg r0 k (Pfn r0 k m) R) t /\ Pfn r0 k m <= t) ->
      forall n m R, exists t, Reaches tm (Scfg r0 k m (rep n 1 R)) (Scfg r0 k (iter (Pfn r0 k) n m) R) t /\
                              (1 <= n -> iter (Pfn r0 k) n m <= t)).
    { intros r0 k Hstep n. induction n as [| p IHp]; intros m R.
      - exists 0. split; [apply reaches_zero | lia].
      - destruct p as [| p'].
        + destruct (Hstep m R) as [t1 [H1 Hle1]].
          exists t1. split; [exact H1 | intros _; exact Hle1].
        + destruct (Hstep m (rep (S p') 1 R)) as [t1 [H1 _]].
          destruct (IHp (Pfn r0 k m) R) as [t2 [H2 Hle2]].
          exists (t1 + t2).
          replace (iter (Pfn r0 k) (S (S p')) m) with (iter (Pfn r0 k) (S p') (Pfn r0 k m))
            by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
          split; [eapply reaches_trans; eassumption | intros _; pose proof (Hle2 ltac:(lia)); lia]. }
    assert (Hexit : forall r0,
      (forall k m R, exists t, Reaches tm (Scfg r0 k m (1 :: R)) (Scfg r0 k (Pfn r0 k m) R) t /\ Pfn r0 k m <= t) ->
      forall k M R, exists t, Reaches tm (Scfg r0 k M (4 :: R)) (Scfg (S r0) 0 (PexitOf (Pfn r0) k M) R) t /\
                              PexitOf (Pfn r0) k M <= t).
    { intros r0 Hstep k. induction k as [| j IH]; intros M R.
      - apply fwp2_exit_zero.
      - destruct (bounce_S_2k r0 j (rep (2 * M + 1) 1 (4 :: R))) as [t3 H3].
        destruct (Hrep r0 j (Hstep j) (2 * M + 2) 0 (4 :: R)) as [t4 [H4 _]].
        assert (HP : iter (Pfn r0 j) (2 * M + 2) 0 = Pfn r0 (S j) M) by (destruct r0; reflexivity).
        rewrite HP in H4.
        destruct (IH (Pfn r0 (S j) M) R) as [t5 [H5 Hle5]].
        eexists. split.
        + eapply reaches_trans; [eapply reaches_trans; [| exact H4] | exact H5].
          eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 4 _ _ R (fp_A4 _ hf)) |].
          eapply reaches_trans; [apply (loop_B2_2k tm 3 (fp_kc _ hf) j (2 * M + 1) (rep r0 5 []) (4 :: R)) |].
          replace (rep (2 * M + 2) 1 (4 :: R)) with (1 :: rep (2 * M + 1) 1 (4 :: R))
            by (replace (2 * M + 2) with (S (2 * M + 1)) by lia; reflexivity).
          exact H3.
        + change (PexitOf (Pfn r0) (S j) M) with (PexitOf (Pfn r0) j (Pfn r0 (S j) M)). lia. }
    induction r as [| r' [IHstep IHexit]].
    - assert (H0 : forall k m R, exists t, Reaches tm (Scfg 0 k m (1 :: R)) (Scfg 0 k (Pfn 0 k m) R) t /\ Pfn 0 k m <= t).
      { induction k as [| j IH]; intros m R.
        - exists (8 * m + 9). split; [apply (kropitz_K1 tm 3 (fp_kc _ hf)) | change (Pfn 0 0 m) with (S m); lia].
        - destruct (Hrep 0 j IH (2 * m + 2) 0 (3 :: R)) as [t2 [H2 Hle2]].
          eexists. split.
          + eapply reaches_trans; [eapply reaches_trans; [apply (kropitz_K2 tm 3 (fp_kc _ hf) j m R) | exact H2] |].
            apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 0 1 _ _ 3 R (kc_A3 _ _ (fp_kc _ hf))).
          + pose proof (Hle2 ltac:(lia)). change (Pfn 0 (S j) m) with (iter (Pfn 0 j) (2 * m + 2) 0). lia. }
      split; [exact H0 | apply Hexit, H0].
    - assert (HS : forall k m R, exists t, Reaches tm (Scfg (S r') k m (1 :: R)) (Scfg (S r') k (Pfn (S r') k m) R) t /\ Pfn (S r') k m <= t).
      { induction k as [| j IH]; intros m R.
        - destruct (fwp2_level0_entry r' m R) as [t1 H1].
          destruct (IHexit (2 * m + 2) 0 R) as [t2 [H2 Hle2]].
          exists (t1 + t2). split; [eapply reaches_trans; eassumption | change (Pfn (S r') 0 m) with (PexitOf (Pfn r') (2 * m + 2) 0); lia].
        - destruct (bounce_S_2k (S r') j (rep (2 * m + 1) 1 (3 :: R))) as [t3 H3].
          destruct (Hrep (S r') j IH (2 * m + 2) 0 (3 :: R)) as [t4 [H4 Hle4]].
          eexists. split.
          + eapply reaches_trans; [eapply reaches_trans; [| exact H4] |].
            * eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 2 2 1 _ _ R (kc_A1 _ _ (fp_kc _ hf))) |].
              eapply reaches_trans; [apply (loop_B2_2k tm 3 (fp_kc _ hf) j (2 * m + 1) (rep (S r') 5 []) (3 :: R)) |].
              replace (rep (2 * m + 2) 1 (3 :: R)) with (1 :: rep (2 * m + 1) 1 (3 :: R))
                by (replace (2 * m + 2) with (S (2 * m + 1)) by lia; reflexivity).
              exact H3.
            * apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 0 1 _ _ 3 R (kc_A3 _ _ (fp_kc _ hf))).
          + pose proof (Hle4 ltac:(lia)). change (Pfn (S r') (S j) m) with (iter (Pfn (S r') j) (2 * m + 2) 0). lia. }
      split; [exact HS | apply Hexit, HS].
  Qed.

  Theorem fwp2_step : forall r k m R,
    exists t, Reaches tm (Scfg r k m (1 :: R)) (Scfg r k (Pfn r k m) R) t /\ Pfn r k m <= t.
  Proof. intro r. apply (proj1 (fwp2_main r)). Qed.

  Theorem fwp2_empty3 : forall r R,
    exists t, Reaches tm (mkCfgR (Some 0) (2 :: rep (S r) 5 []) (1 :: R))
                         (Scfg (S r) 0 (Pempty r) R) t /\ Pempty r <= t.
  Proof.
    intros r R.
    destruct (fwp2_empty3_entry r R) as [t1 H1].
    destruct (proj2 (fwp2_main r) 1 0 R) as [t2 [H2 Hle2]].
    exists (t1 + t2). split; [eapply reaches_trans; eassumption | unfold Pempty; lia].
  Qed.

End Fwp2Lemmas.
