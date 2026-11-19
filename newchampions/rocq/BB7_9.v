(*
  rocq/BB7_9.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 9):
    TM: 8RG3LB6LA2RA4LB5RC5LA2LG7LE_1RZ3RB1LD2RA3LF5RB6LD1RZ5LD_3RB1LB3LC2RC4LC1LE5RB3RF3RD_3RB3RE3LC2RC7LF3RD1LA2RA8LE_5RB3RE8LA4LC3LG5LE1RZ1RZ3LA_5RB5RB2RA1LF8LF5LF1RZ1RF8LC_5LF4RG7LA1LG8RC5LG1LC4RF8RG
    Domain: BB(7, 9) (7 states, 9 symbols)
    Previous best dominated bounds: BB(7, 8) > f_{ω^2+2}(7), BB(6, 9) > f_{ω×2+3}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

Definition bb79 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 8RG 3LB 6LA 2RA 4LB 5RC 5LA 2LG 7LE *)
  | 0, 0 => Some (mkAction 8 DR (Some 6))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 6 DL (Some 0))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 5 DR (Some 2))
  | 0, 6 => Some (mkAction 5 DL (Some 0))
  | 0, 7 => Some (mkAction 2 DL (Some 6))
  | 0, 8 => Some (mkAction 7 DL (Some 4))
  (* State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD 1RZ 5LD *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 6 DL (Some 3))
  | 1, 7 => Some (mkAction 1 DR None)
  | 1, 8 => Some (mkAction 5 DL (Some 3))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB 3RF 3RD *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 5 DR (Some 1))
  | 2, 7 => Some (mkAction 3 DR (Some 5))
  | 2, 8 => Some (mkAction 3 DR (Some 3))
  (* State D (3): 3RB 3RE 3LC 2RC 7LF 3RD 1LA 2RA 8LE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 7 DL (Some 5))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 1 DL (Some 0))
  | 3, 7 => Some (mkAction 2 DR (Some 0))
  | 3, 8 => Some (mkAction 8 DL (Some 4))
  (* State E (4): 5RB 3RE 8LA 4LC 3LG 5LE 1RZ 1RZ 3LA *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 8 DL (Some 0))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 1 DR None)
  | 4, 7 => Some (mkAction 1 DR None)
  | 4, 8 => Some (mkAction 3 DL (Some 0))
  (* State F (5): 5RB 5RB 2RA 1LF 8LF 5LF 1RZ 1RF 8LC *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 2 DR (Some 0))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 8 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 1 DR None)
  | 5, 7 => Some (mkAction 1 DR (Some 5))
  | 5, 8 => Some (mkAction 8 DL (Some 2))
  (* State G (6): 5LF 4RG 7LA 1LG 8RC 5LG 1LC 4RF 8RG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 7 DL (Some 0))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 8 DR (Some 2))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 1 DL (Some 2))
  | 6, 7 => Some (mkAction 4 DR (Some 5))
  | 6, 8 => Some (mkAction 8 DR (Some 6))
  | _, _ => None
  end.

Lemma bb79_valid : ValidTM 7 9 bb79.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 7 (destruct s as [| s]; [
      do 9 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 7 (destruct s as [| s]; [
      do 9 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb79_core : Fwp2_7Core bb79.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_G_7 : forall n L R,
  Reaches bb79 (mkCfgR (Some 6) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 6) L (2 :: rep n 2 R)) (3 * n).
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 3 2 _ _ R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (7 :: R) eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_E_8 : forall n L R,
  Reaches bb79 (mkCfgR (Some 4) (rep n 3 L) (2 :: R))
               (mkCfgR (Some 4) L (2 :: rep n 7 R)) (3 * n).
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 7 3 2 _ _ R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 1 _ _ 3 (8 :: R) eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 8 _ _ R eq_refl) |].
  specialize (IH L (7 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma reload_7 : forall r m R,
  exists t, Reaches bb79 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r) 0 0 (rep (2 * m + 1) 2 R)) t.
Proof.
  intros r m R. eexists.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 7 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_G_7 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 6 5 2 _ _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 7 _ eq_refl) |].
  apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 5 1 _ _ 2 _ eq_refl).
Qed.

Lemma reload_8 : forall r m R,
  exists t, Reaches bb79 (Scfg (S r) 0 m (8 :: R)) (Scfg (S r) 0 0 (rep (2 * m + 1) 7 R)) t.
Proof.
  intros r m R. eexists.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 6 2 8 _ _ R eq_refl) |].
  eapply reaches_trans; [apply (loop_E_8 (2 * m + 1) (rep (S r) 5 []) (7 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 4 7 5 2 _ _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 0 4 _ _ 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 2 2 _ _ 8 _ eq_refl) |].
  apply steps_one. unfold Scfg. apply (step_mkCfgR_R _ 3 1 _ _ 7 _ eq_refl).
Qed.

Definition H7 (m : nat) : nat := iter H2_7 (2 * m) 17.
Definition H8 (m : nat) : nat := iter H7 (2 * m) 17.

Lemma H7_mono : forall x y, x <= y -> H7 x <= H7 y.
Proof.
  intros x y Hxy. unfold H7.
  apply iter_mono_steps; [intro z; unfold H2_7; pose proof (Pempty_ge (2 * z + 1)); lia | lia].
Qed.

Lemma H7_gt : forall m, 1 <= m -> f_omega2_plus 1 m < H7 m.
Proof.
  intros m Hm. unfold H7.
  apply (climb_double H2_7 f_omega2 17 ltac:(lia) H2_7_mono H2_7_inc H2_7_gt (fOmega2_props 1 0 0) m Hm).
Qed.

Lemma H7_inc : forall m, 1 <= m -> S m <= H7 m.
Proof.
  intros m Hm. pose proof (H7_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 1) m).
  change (f_omega2_plus 1 m) with (fOmega2 1 0 1 m) in *. lia.
Qed.

Lemma H8_mono : forall x y, x <= y -> H8 x <= H8 y.
Proof.
  intros x y Hxy. unfold H8.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H7_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H8_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H8 m.
Proof.
  intros m Hm. unfold H8.
  apply (climb_double H7 (f_omega2_plus 1) 17 ltac:(lia) H7_mono H7_inc H7_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma rule_7 : forall r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (7 :: R)) (Scfg (S r') 0 m' R) t /\
    H7 m <= m' /\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_7 r m R) as [t0 H0].
  replace (2 * m + 1) with (S (2 * m)) in H0 by lia.
  destruct (rule_2_7 bb79 bb79_core r 0 (rep (2 * m) 2 R)) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_17 : 17 <= m1) by (pose proof H2_7_0_ge; lia).
  destruct m as [| m'].
  - exists r1, m1, (t0 + t1). split; [eapply reaches_trans; eassumption | split; [change (H7 0) with 17; lia | lia]].
  - destruct (rule_2_7_rep bb79 bb79_core (2 * S m') r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists r2, m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    + unfold H7. eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_7_mono | exact Hm1_17] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_7_rep : forall n r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (rep n 7 R)) (Scfg (S r') 0 m' R) t /\
    iter H7 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_7 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_7 r m (rep (S p') 7 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H7 (S (S p')) m) with (iter H7 (S p') (H7 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_8 : forall r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (8 :: R)) (Scfg (S r') 0 m' R) t /\
    H8 m <= m' /\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_8 r m R) as [t0 H0].
  replace (2 * m + 1) with (S (2 * m)) in H0 by lia.
  destruct (rule_7 r 0 (rep (2 * m) 7 R)) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
  assert (Hm1_17 : 17 <= m1) by (change (H7 0) with 17 in Hm1; lia).
  destruct m as [| m'].
  - exists r1, m1, (t0 + t1). split; [eapply reaches_trans; eassumption | split; [change (H8 0) with 17; lia | lia]].
  - destruct (rule_7_rep (2 * S m') r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
    exists r2, m2, ((t0 + t1) + t2). split; [eapply reaches_trans; [eapply reaches_trans; eassumption | exact H2r] | split].
    + unfold H8. eapply Nat.le_trans; [apply iter_mono_arg; [apply H7_mono | exact Hm1_17] | exact Hm2].
    + pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma rule_8_rep : forall n r m R,
  exists r' m' t, Reaches bb79 (Scfg (S r) 0 m (rep n 8 R)) (Scfg (S r') 0 m' R) t /\
    iter H8 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_8 r m R) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists r1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_8 r m (rep (S p') 8 R)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH r1 m1 R) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H8 (S (S p')) m) with (iter H8 (S p') (H8 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H8_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb79_bootstrap :
  Reaches bb79 initConfig (Scfg 1 0 0 (rep 8 8 [5])) 74.
Proof. vm_compute. reflexivity. Qed.

Theorem bb79_halts_gt_f_omega2_plus_3_7 :
  ValidTM 7 9 bb79 /\ exists t, HaltsIn bb79 initConfig t /\ f_omega2_plus 3 7 < t.
Proof.
  split; [exact bb79_valid |].
  pose proof bb79_bootstrap as Hboot.
  destruct (rule_8 0 0 (rep 7 8 [5])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_7 : 7 <= m1) by (change (H8 0) with 17 in Hm1; lia).
  destruct (rule_8_rep 7 r1 m1 [5]) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (rule_halt_5_7 bb79 bb79_core r2 m2) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) Hhalt) as Hreach.
  pose proof (iter_strict_dom H8 (f_omega2_plus 2) 1 H8_gt (fOmega2_props 1 0 2) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H8 H8_mono 7 7 m1 Hm1_7) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 3 7) with (iter (f_omega2_plus 2) 7 7). lia.
Qed.

Print Assumptions bb79_halts_gt_f_omega2_plus_3_7.
