(*
  rocq/BB6_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(6, 8):
    TM: 5RE3LB7LF2RA4LB6LF1RZ5RF_5LE3RB1LD2RA3LF7RC3LB3RA_3RB1LB3LC2RC4LC0LE6LE5LF_3RB6RD3LC2RC5LA3RE2LE1LB_5RC3RE2RA4LC6RA5LA2LE3RE_5RB7RD1LF1LF5RA5RF5LE0RD
    Domain: BB(6, 8) (6 states, 8 symbols)
    Previous best dominated bounds: BB(6, 7) > f_{ω×2+1}(6), BB(4, 8) > f_{ω+4}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+2}(11)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwm2.
Import ListNotations.

Definition bb68 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 5RE 3LB 7LF 2RA 4LB 6LF 1RZ 5RF *)
  | 0, 0 => Some (mkAction 5 DR (Some 4))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 7 DL (Some 5))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 6 DL (Some 5))
  | 0, 6 => Some (mkAction 1 DR None)
  | 0, 7 => Some (mkAction 5 DR (Some 5))
  (* State B (1): 5LE 3RB 1LD 2RA 3LF 7RC 3LB 3RA *)
  | 1, 0 => Some (mkAction 5 DL (Some 4))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 7 DR (Some 2))
  | 1, 6 => Some (mkAction 3 DL (Some 1))
  | 1, 7 => Some (mkAction 3 DR (Some 0))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 0LE 6LE 5LF *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 0 DL (Some 4))
  | 2, 6 => Some (mkAction 6 DL (Some 4))
  | 2, 7 => Some (mkAction 5 DL (Some 5))
  (* State D (3): 3RB 6RD 3LC 2RC 5LA 3RE 2LE 1LB *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 6 DR (Some 3))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 5 DL (Some 0))
  | 3, 5 => Some (mkAction 3 DR (Some 4))
  | 3, 6 => Some (mkAction 2 DL (Some 4))
  | 3, 7 => Some (mkAction 1 DL (Some 1))
  (* State E (4): 5RC 3RE 2RA 4LC 6RA 5LA 2LE 3RE *)
  | 4, 0 => Some (mkAction 5 DR (Some 2))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 0))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 6 DR (Some 0))
  | 4, 5 => Some (mkAction 5 DL (Some 0))
  | 4, 6 => Some (mkAction 2 DL (Some 4))
  | 4, 7 => Some (mkAction 3 DR (Some 4))
  (* State F (5): 5RB 7RD 1LF 1LF 5RA 5RF 5LE 0RD *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 7 DR (Some 3))
  | 5, 2 => Some (mkAction 1 DL (Some 5))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DR (Some 0))
  | 5, 5 => Some (mkAction 5 DR (Some 5))
  | 5, 6 => Some (mkAction 5 DL (Some 4))
  | 5, 7 => Some (mkAction 0 DR (Some 3))
  | _, _ => None
  end.

Lemma bb68_valid : ValidTM 6 8 bb68.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 6 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 6 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb68_fwm2 : Fwm2Core bb68.
Proof. constructor; [constructor; reflexivity | ..]; reflexivity. Qed.

Local Lemma rep_add : forall a b s R, rep a s (rep b s R) = rep (a + b) s R.
Proof. induction a as [| p IH]; intros b s R; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Local Lemma loop_F2 : forall n L R,
  Reaches bb68 (mkCfgR (Some 5) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 5) L (2 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 2 2 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_F3 : forall n L R,
  Reaches bb68 (mkCfgR (Some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_D1 : forall n L R,
  Reaches bb68 (mkCfgR (Some 3) L (rep n 1 R))
               (mkCfgR (Some 3) (rep n 6 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 3 5 _ L 1 _ eq_refl) |].
  specialize (IH (6 :: L) R). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_B6 : forall n L R,
  Reaches bb68 (mkCfgR (Some 1) (rep n 6 L) (6 :: R))
               (mkCfgR (Some 1) L (6 :: rep n 3 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 6 6 _ _ R eq_refl) |].
  specialize (IH L (3 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_E6 : forall n L R,
  Reaches bb68 (mkCfgR (Some 4) (rep n 6 L) (6 :: R))
               (mkCfgR (Some 4) L (6 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 1 6 6 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma sweep_FD : forall k m mark R,
  exists t, Reaches bb68
    (mkCfgR (Some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: mark :: R))
    (mkCfgR (Some 3) (rep (2 * m + k + 1) 6 [7; 5]) (mark :: R)) t.
Proof.
  intros k m mark R. eexists. eapply reaches_trans.
  - eapply reaches_trans; [apply (loop_F2 k (rep (2 * m + 1) 3 [5]) (mark :: R)) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    change (1 :: rep k 1 (mark :: R)) with (rep (S k) 1 (mark :: R)).
    apply (loop_F3 (2 * m) [5] (rep (S k) 1 (mark :: R))).
  - rewrite rep_add. replace (2 * m + S k) with (2 * m + k + 1) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 5 3 _ [] _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 5 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 6 _ [5] 1 _ eq_refl) |].
    apply (loop_D1 (2 * m + k + 1) [7; 5] (mark :: R)).
Qed.

Lemma reload_2 : forall k m R,
  exists t, Reaches bb68 (B5cfg k m (2 :: R)) (B5cfg (2 * m + k) 0 (1 :: R)) t.
Proof.
  intros k m R. destruct (sweep_FD k m 7 R) as [ts Hs].
  eexists. eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 2 _ _ R eq_refl) |].
  eapply reaches_trans; [exact Hs |].
  replace (2 * m + k + 1) with (S (2 * m + k)) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 0 6 7 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_B6 (2 * m + k) [7; 5] (1 :: R)) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 1 2 7 6 _ [5] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ [5] 7 _ eq_refl) |].
  change (3 :: rep (2 * m + k) 3 (1 :: R)) with (rep (S (2 * m + k)) 3 (1 :: R)).
  unfold B5cfg. apply (loop_A3 bb68 3 (fw_kc _ bb68_fwm2) (S (2 * m + k)) [3; 5] (1 :: R)).
Qed.

Lemma reload_5 : forall k m R,
  exists t, Reaches bb68 (B5cfg k m (5 :: R)) (B5cfg 0 0 (rep (2 * m + k + 1) 2 R)) t.
Proof.
  intros k m R. destruct (sweep_FD k m 6 R) as [ts Hs].
  eexists. eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 5 _ _ R eq_refl) |].
  eapply reaches_trans; [exact Hs |].
  replace (2 * m + k + 1) with (S (2 * m + k)) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 1 6 6 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_E6 (2 * m + k) [7; 5] (2 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 1 7 6 _ [5] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 4 2 _ [5] 7 _ eq_refl) |].
  apply steps_one. unfold B5cfg.
  apply (step_mkCfgR_R _ 4 1 _ [3; 5] 2 _ eq_refl).
Qed.

Definition H2 (m : nat) : nat := Wfn (2 * m) 0.
Definition H5 (m : nat) : nat := iter H2 (2 * m) 15.

Lemma H2_mono : forall x y, x <= y -> H2 x <= H2 y.
Proof. intros x y Hxy. unfold H2. apply Wfn_mono_k; lia. Qed.

Lemma H2_inc : forall m, 1 <= m -> S m <= H2 m.
Proof. intros m _. unfold H2. pose proof (Wfn_zero_ge (2 * m)). lia. Qed.

Lemma H2_gt : forall m, 1 <= m -> f_omega_mul2 m < H2 m.
Proof.
  intros m Hm. unfold H2.
  pose proof (Wfn_succ_zero_gt_f_omega_mul2 m).
  pose proof (Wfn_mono_k (S m) (2 * m) 0 ltac:(lia)). lia.
Qed.

Lemma H5_mono : forall x y, x <= y -> H5 x <= H5 y.
Proof.
  intros x y Hxy. unfold H5.
  apply iter_mono_steps; [intro z; unfold H2; pose proof (Wfn_zero_ge (2 * z)); lia | lia].
Qed.

Lemma H5_gt : forall m, 1 <= m -> f_omega_mul2_plus 1 m < H5 m.
Proof.
  intros m Hm. unfold H5.
  apply (climb_double H2 f_omega_mul2 15 ltac:(lia) H2_mono H2_inc H2_gt (fOmegaMul_props 2 0) m Hm).
Qed.

Lemma rule_2 : forall k m R,
  exists k' m' t, Reaches bb68 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t /\ H2 m <= m' /\ m' <= t.
Proof.
  intros k m R.
  destruct (reload_2 k m R) as [t1 H1].
  destruct (fwm2_step bb68 bb68_fwm2 (2 * m + k) 0 R) as [t2 [H2s Hle2]].
  exists (2 * m + k), (Wfn (2 * m + k) 0), (t1 + t2).
  split; [eapply reaches_trans; eassumption | split; [unfold H2; apply Wfn_mono_k; lia | lia]].
Qed.

Lemma rule_2_rep : forall n k m R,
  exists k' m' t, Reaches bb68 (B5cfg k m (rep n 2 R)) (B5cfg k' m' R) t /\
    iter H2 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros k m R.
  - exists k, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_2 k m R) as [k1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists k1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_2 k m (rep (S p') 2 R)) as [k1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH k1 m1 R) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists k2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H2 (S (S p')) m) with (iter H2 (S p') (H2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_5 : forall k m R,
  exists k' m' t, Reaches bb68 (B5cfg k m (5 :: R)) (B5cfg k' m' R) t /\ H5 m <= m' /\ m' <= t.
Proof.
  intros k m R.
  destruct (reload_5 k m R) as [t0 H0].
  replace (2 * m + k + 1) with (S (2 * m + k)) in H0 by lia.
  destruct (rule_2 0 0 (rep (2 * m + k) 2 R)) as [k1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_15 : 15 <= m1) by (assert (H15 : H2 0 = 15) by reflexivity; lia).
  destruct (2 * m + k) as [| r] eqn:Hmk.
  - assert (Hm0 : m = 0) by lia. subst m.
    exists k1, m1, (t0 + t1). split; [| split].
    + eapply reaches_trans; eassumption.
    + change (H5 0) with 15. lia.
    + lia.
  - destruct (rule_2_rep (S r) k1 m1 R) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists k2, m2, ((t0 + t1) + t2). split; [| split].
    + eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r].
    + unfold H5.
      eapply Nat.le_trans; [apply (iter_mono_steps H2 (fun z => ltac:(unfold H2; pose proof (Wfn_zero_ge (2 * z)); lia)) (2 * m) (S r) 15 ltac:(lia)) |].
      eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_mono | exact Hm1_15] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_5_rep : forall n k m R,
  exists k' m' t, Reaches bb68 (B5cfg k m (rep n 5 R)) (B5cfg k' m' R) t /\
    iter H5 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros k m R.
  - exists k, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_5 k m R) as [k1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists k1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_5 k m (rep (S p') 5 R)) as [k1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH k1 m1 R) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists k2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H5 (S (S p')) m) with (iter H5 (S p') (H5 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H5_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb68_bootstrap :
  Reaches bb68 initConfig (B5cfg 0 0 (2 :: rep 11 5 [6])) 210.
Proof. vm_compute. reflexivity. Qed.

Theorem bb68_halts_gt_f_omega_mul2_plus_2_11 :
  ValidTM 6 8 bb68 /\ exists t, HaltsIn bb68 initConfig t /\ f_omega_mul2_plus 2 11 < t.
Proof.
  split; [exact bb68_valid |].
  pose proof bb68_bootstrap as Hboot.
  destruct (rule_2 0 0 (rep 11 5 [6])) as [k1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_ge : 11 <= m1) by (assert (H15 : H2 0 = 15) by reflexivity; lia).
  destruct (rule_5_rep 11 k1 m1 [6]) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  assert (Hhalt : step bb68 (B5cfg k2 m2 [6]) =
    Some (mkCfgR None (1 :: rep (S k2) 2 (rep (2 * m2 + 1) 3 [5])) [])).
  { apply (step_mkCfgR_R _ 0 0 _ _ 6 [] eq_refl). }
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r)
    (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H5 (f_omega_mul2_plus 1) 1 H5_gt
    (fOmegaMul_props 2 1) 11 11 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H5 H5_mono 11 11 m1 Hm1_ge) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  exists (((210 + t1) + t2) + 1). split.
  - eexists; split; [exact Hreach | reflexivity].
  - change (f_omega_mul2_plus 2 11) with (iter (f_omega_mul2_plus 1) 11 11). lia.
Qed.

Print Assumptions bb68_halts_gt_f_omega_mul2_plus_2_11.
